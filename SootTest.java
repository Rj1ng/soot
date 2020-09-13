import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;
import soot.*;
import soot.jimple.*;
import soot.options.Options;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import java.io.File;
import java.util.*;
import java.util.concurrent.*;


public class SootTest {

    private static String appName = null;
    private static String appPath = null;
    private static String outputDir = null;
    private static String appid = null;
    private static String mch_id = null;
    private static String notify_url = null;
    private static String key = null;
    private static boolean success = false;
    private static Map<String, Integer> clazzMap = null; // 1 for field, 2 for args, 3 for both


    public static void parseInputXML(String xml)
    {
        try{
            clazzMap = new HashMap<>();
            File input = new File(xml);
            DocumentBuilderFactory dbFactory = DocumentBuilderFactory.newInstance();
            DocumentBuilder dBuilder = dbFactory.newDocumentBuilder();
            Document doc = dBuilder.parse(input);
            doc.getDocumentElement().normalize();
            Element root = doc.getDocumentElement();
            appName = root.getElementsByTagName("name").item(0).getTextContent();
            appPath = root.getElementsByTagName("path").item(0).getTextContent();
            NodeList nList = root.getElementsByTagName("property");
            for (int i = 0; i < nList.getLength(); i++)
            {
                Element property = (Element) nList.item(i);
                String clazzName = property.getElementsByTagName("class").item(0).getTextContent();
                if(property.getElementsByTagName("type").item(0).getTextContent().equals("field")){
                    if(clazzMap.containsKey(clazzName))
                        clazzMap.put(clazzName, clazzMap.get(clazzName) | 0x0001);
                    else
                        clazzMap.put(clazzName, 0x0001);
                }//key defined in field
                else{
                    if(clazzMap.containsKey(clazzName))
                        clazzMap.put(clazzName, clazzMap.get(clazzName) | 0x0010);
                    else
                        clazzMap.put(clazzName, 0x0010);
                }//key used in args
            }
        } catch (Exception e) {
            e.printStackTrace();
        }

    }

    public static boolean toAnalyze(SootMethod method){
        SootClass clazz = method.getDeclaringClass();
        if (!clazz.isPhantom()){
            String name = clazz.getName();
            return !name.startsWith("java.") && !name.startsWith("javax.") && !name.startsWith("org.apache.") && !name.startsWith("android.");
        }
        else{
            return false;
        }
    }

    public static boolean fromPrePayIdHostToPutArg(SootMethod entryMethod){
        boolean found = false;
        System.out.println(entryMethod.getSignature());
//        int modifier = entryMethod.getModifiers();
        // Assume the body of the method has been retrieved before transfered, is SSA
        Iterator stmts = entryMethod.retrieveActiveBody().getUnits().snapshotIterator();
        LinkedList<Value> entryList = new LinkedList<>();
        Queue<Value> sourceQueue = new LinkedList<>();
        LinkedList<Value> sinkList = new LinkedList<>();
        HashSet<Value> sourceSet = new HashSet<>();

        while(stmts.hasNext()){
            Stmt stmt = (Stmt)stmts.next();
            System.out.println(stmt.toString());
            // Only handle the case where taint value is transfered to the return value
            // Assume entry appears earlier than usage of entry
            if (stmt instanceof DefinitionStmt){
                System.out.println("DefinitionStmt");
                DefinitionStmt definitionStmt = (DefinitionStmt)stmt;
                Value value = definitionStmt.getRightOp();
                if(checkGetPrePayIdHost(value)){

                    if(value instanceof InvokeExpr){
                        InvokeExpr invokeExpr = (InvokeExpr)value;
                        // Handle Stmt like <java.lang.String: java.lang.String format(java.lang.String,java.lang.Object[])>("https://api.mch.weixin.qq.com/pay/unifiedorder", $r3);
                        switch (invokeExpr.getMethod().getSignature()) {
                            case "<java.lang.String: java.lang.String format(java.lang.String,java.lang.Object[])>":
                                entryList.add(definitionStmt.getLeftOp());
                                break;
                            // Handle Stmt like <org.apache.http.client.methods.HttpPost: void <init>(java.lang.String)>("https://api.mch.weixin.qq.com/pay/unifiedorder");
                            case "<org.apache.http.client.methods.HttpPost: void <init>(java.lang.String)>":
                                List<ValueBox> invokeVariables = definitionStmt.getUseAndDefBoxes();
                                int invokeVariablesSize = invokeVariables.size();
                                if (invokeVariablesSize >= 2) {
                                    ListIterator<ValueBox> invokeVariablesList = invokeVariables.listIterator(invokeVariablesSize - 2);
                                    ValueBox invokeObjBox = invokeVariablesList.next();
                                    Value invokeObj = invokeObjBox.getValue();
                                    entryList.add(invokeObj);
                                }
                                break;
                            default:
                                List<Value> invokeArgs = invokeExpr.getArgs();
                                for (Value arg : invokeArgs) {
                                    System.out.println(arg.toString());
                                    //  Handle Stmt like <com.yueshichina.utils.share.wx.WXUtil: byte[] httpPost(java.lang.String,java.lang.String)>("https://api.mch.weixin.qq.com/pay/unifiedorder", $r2)
                                    if (arg instanceof Local) {
                                        if (!sourceSet.contains(arg)) {
                                            sourceQueue.offer(arg);
                                            sourceSet.add(arg);
                                        }

                                    }
                                }
                                break;
                        }
                    }
                    break;
                }
            }
            else if(stmt instanceof InvokeStmt){
                System.out.println("InvokeStmt");
                InvokeStmt invokeStmt = (InvokeStmt)stmt;
                InvokeExpr invokeExpr = invokeStmt.getInvokeExpr();
                if(checkGetPrePayIdHost(invokeExpr)){
                    List<Value> invokeArgs = invokeExpr.getArgs();
                    for (Value arg: invokeArgs){
                        System.out.println(arg.toString());
                        if (arg instanceof Local){
                            if(!sourceSet.contains(arg)){
                                sourceQueue.offer(arg);
                                sourceSet.add(arg);
                            }
                        }
                    }
                    break;
                }
            }
        }
        // entryList contains objects links to the request url
        // sourceQueue contains objects links to request content

        stmts = entryMethod.retrieveActiveBody().getUnits().snapshotIterator();
        Value entry = null;
        while(stmts.hasNext()){
            Stmt stmt = (Stmt)stmts.next();
            System.out.println(stmt.toString());

            if (stmt instanceof DefinitionStmt){
                DefinitionStmt definitionStmt = (DefinitionStmt)stmt;
                Value value = definitionStmt.getRightOp();

                if (value instanceof InvokeExpr){
                    InvokeExpr invokeExpr = (InvokeExpr)value;
                    List<Value> invokeArgs = invokeExpr.getArgs();
                    boolean sourceFound = false;
                    // handle stmt like <com.zyc.common.wxpay.Util: byte[] httpPost(java.lang.String,java.lang.String)>($r2, $r6_1)
                    for (Value arg : invokeArgs) {
                        for (Value iterValue : entryList) {
                            //System.out.println("Args:");
                            //System.out.println(iterValue.toString());
                            if (arg.equivTo(iterValue)) {
                                sourceFound = true;
                                entry = iterValue;
                                break;
                            }
                        }
                    }

                    if(sourceFound){
                        for (Value arg : invokeArgs) {
                            if (arg instanceof Local) {
                                if (!arg.equivTo(entry)) {
                                    if (!sourceSet.contains(arg)) {
                                        sourceQueue.offer(arg);
                                        sourceSet.add(arg);
                                    }
                                }
                            }
                        }
                    }
                }
            }


/*
System.out.println("Value of Stmt");
List<ValueBox> valueBoxList = stmt.getUseBoxes();
for (ValueBox valueBox : valueBoxList){
System.out.println(valueBox.getValue().toString());
}
*/

            else if(stmt instanceof InvokeStmt){
                InvokeStmt invokeStmt = (InvokeStmt)stmt;
                InvokeExpr invokeExpr = invokeStmt.getInvokeExpr();
                if(invokeExpr.getMethod().getSignature().equals("<org.apache.http.client.methods.HttpPost: void setEntity(org.apache.http.HttpEntity)>")){
                    // handle stmt like virtualinvoke $r4.<org.apache.http.client.methods.HttpPost: void setEntity(org.apache.http.HttpEntity)>($r7)
                    List<Value> invokeArgs = invokeExpr.getArgs();
                    for (Value arg: invokeArgs){
//                        System.out.println("Args:");
//                        System.out.println(arg.toString());
                        if (arg instanceof Local){
                            if(!sourceSet.contains(arg)){
                                sourceQueue.offer(arg);
                                sourceSet.add(arg);
                            }
                        }
                    }
                }
            }
        }

        /*
        System.out.println("SourceQueue!");
           while(!sourceQueue.isEmpty()){
            System.out.println(sourceQueue.poll().toString());
        }
        */

        /*
         * sourceQueue contains the transmission list of order info
         */
        while(!sourceQueue.isEmpty() && (!found)){
            Value source = sourceQueue.poll();
            Queue<SootMethod> taintQueue = new LinkedList<>();
            stmts = entryMethod.retrieveActiveBody().getUnits().snapshotIterator();
            while(stmts.hasNext()){
                Stmt stmt = (Stmt)stmts.next();
                if (stmt instanceof DefinitionStmt){
                    DefinitionStmt definitionStmt = (DefinitionStmt)stmt;
                    Value left = definitionStmt.getLeftOp();
                    if (left.equivTo(source)){
                        Value right = definitionStmt.getRightOp();
                        // ignore taint transfered to field of a class
                        if (right instanceof InvokeExpr){
                            InvokeExpr invokeExpr = (InvokeExpr)right;
                            if(toAnalyze(invokeExpr.getMethod()))
                                taintQueue.offer(invokeExpr.getMethod());
                            List<Value> invokeArgs = invokeExpr.getArgs();
                            List<ValueBox> invokeVariables = definitionStmt.getUseAndDefBoxes();
                            int invokeVariablesSize = invokeVariables.size();
                            int invokeArgsSize = invokeArgs.size();
                            System.out.println("DefineValueBox");
                            for (ValueBox valueBox : invokeVariables){
                                System.out.println(valueBox.getValue().toString());
                            }
                            /*
                            Location of invokeStmt and DefinitionStmt is different
                            DefineValueBox
                            $r5
                            virtualinvoke $r4.<java.lang.String: byte[] getBytes()>()
                            $r4
                            */
                            if ((invokeArgsSize + 1 < invokeVariablesSize) && invokeVariablesSize >= 3){
                                ListIterator<ValueBox> invokeVariablesList = invokeVariables.listIterator(invokeVariablesSize-1);
                                ValueBox invokeObjBox = invokeVariablesList.next();
                                Value invokeObj = invokeObjBox.getValue();
                                if(invokeObj instanceof Local){
                                    if (!sourceSet.contains(invokeObj)){
                                        sourceQueue.offer(invokeObj);
                                        sourceSet.add(invokeObj);
                                    }
                                }
                            }
                        }
                        else if(right instanceof Local){
                            if(!sourceSet.contains(right)){
                                sourceQueue.offer(right);
                                sourceSet.add(right);
                            }
                        }
                    }
                }
                else if(stmt instanceof InvokeStmt){
                    InvokeStmt invokeStmt = (InvokeStmt)stmt;
                    InvokeExpr invokeExpr = invokeStmt.getInvokeExpr();
                    List<Value> invokeArgs = invokeExpr.getArgs();
                    List<ValueBox> invokeVariables = invokeStmt.getUseAndDefBoxes();
                    System.out.println("InvokeValueBox");
                    for (ValueBox valueBox : invokeVariables){
                        System.out.println(valueBox.getValue().toString());
                    }
                    /*
                    Location of invokeStmt and DefinitionStmt is different
                    InvokeValueBox
                    $r5
                    "ISO8859-1"
                    $r2
                    specialinvoke $r2.<java.lang.String: void <init>(byte[],java.lang.String)>($r5, "ISO8859-1")
                    */
                    int invokeVariablesSize = invokeVariables.size();
                    int invokeArgsSize = invokeArgs.size();
                    if ((invokeArgsSize + 1 < invokeVariablesSize) && invokeVariablesSize >= 2){
                        ListIterator<ValueBox> invokeVariablesList = invokeVariables.listIterator(invokeVariablesSize-2);
                        ValueBox invokeObjBox = invokeVariablesList.next();
                        Value invokeObj = invokeObjBox.getValue();
                        System.out.println("Compare:");
                        System.out.println(invokeObj.toString());
                        assert source != null;
                        System.out.println(source.toString());
                        if (invokeObj.equivTo(source)){
                            for (Value arg : invokeArgs){
                                if(arg instanceof Local){
                                    if(!sourceSet.contains(arg)){
                                        sourceSet.add(arg);
                                        sourceQueue.offer(arg);
                                    }
                                }
                            }

                        }
                    }
                }
            }

//                System.out.println("TaintQueue!");
//                while(!taintQueue.isEmpty()){
//                    System.out.println(taintQueue.poll().toString());
//                }


            while((!taintQueue.isEmpty()) && (!found)){
                SootMethod taintMethod = taintQueue.poll();
                assert taintMethod != null;
                System.out.println(taintMethod.getSignature());
//                try {
                stmts = taintMethod.retrieveActiveBody().getUnits().snapshotIterator();
                int count = 0;
                Deque<Stmt> stmtPool = new LinkedList<>();
                while(stmts.hasNext()){
                    Stmt stmt = (Stmt)stmts.next();
                    System.out.println(stmt.toString());
                    /*
                     * naive search, just follow the demo
                     * But maybe some other data structs.
                    */
                    if (stmt instanceof InvokeStmt){
                        InvokeStmt invokeStmt = (InvokeStmt)stmt;
                        InvokeExpr invokeExpr = invokeStmt.getInvokeExpr();
                        //System.out.println(invokeExpr.getMethod().getSignature());
                        if(invokeExpr.getMethod().getSignature().equals("<org.apache.http.message.BasicNameValuePair: void <init>(java.lang.String,java.lang.String)>")){
                            found = true;
                            Value arg_1 = invokeExpr.getArg(0);
                            Value arg_2 = invokeExpr.getArg(1);
                            if(arg_1 instanceof StringConstant){
                                StringConstant constant = (StringConstant)arg_1;
                                String arg_1_str = constant.toString();
                                switch (arg_1_str) {
                                    case "\"appid\"":
                                        appid = getItemValue(arg_2);
                                        break;
                                    case "\"mch_id\"":
                                        mch_id = getItemValue(arg_2);
                                        break;
                                    case "\"notify_url\"":
                                        notify_url = getItemValue(arg_2);
                                        break;
                                    case "\"sign\"":
                                        while (!stmtPool.isEmpty()) {
                                            Stmt iterStmt = stmtPool.pollLast();
                                            if (iterStmt instanceof DefinitionStmt) {
                                                DefinitionStmt iterDefinitionStmt = (DefinitionStmt) iterStmt;
                                                Value iterLeft = iterDefinitionStmt.getLeftOp();
                                                if (iterLeft.equivTo(arg_2)) {
                                                    key = getKeyValue(iterStmt);
                                                }
                                            }
                                        }
                                        break;
                                }
                            }
                        }
                        else{
                            if(toAnalyze(invokeExpr.getMethod()))
                                taintQueue.offer(invokeExpr.getMethod());
                        }
                    }
                    else if(stmt instanceof DefinitionStmt){
                        DefinitionStmt definitionStmt = (DefinitionStmt)stmt;
                        Value right = definitionStmt.getRightOp();
                        if (right instanceof InvokeExpr){
                            InvokeExpr invokeExpr = (InvokeExpr)right;
                            if(toAnalyze(invokeExpr.getMethod()))
                                taintQueue.offer(invokeExpr.getMethod());
                        }
                    }
                    if(count < 5) {
                        stmtPool.offerLast(stmt);
                    }
                    else {
                        stmtPool.pollFirst();
                        stmtPool.offerLast(stmt);
                    }
                    count = count + 1;
                }
/*
}catch(Exception e){
e.printStackTrace();
}
*/
            }
            if(found){
                System.out.println(appid);
                System.out.println(mch_id);
                System.out.println(notify_url);
                System.out.println(key);
            }
        }
        return found;
    }

    public static String getItemValue(Value value){
        // cannot handle get-set pair now
        if(value instanceof StringConstant){
            StringConstant constant = (StringConstant)value;
            return constant.toString();
        }
        System.out.println("Could not find item!");
        return null;
    }

    public static String getKeyValue(Stmt stmt){
//        System.out.println(stmt.toString());
        if(stmt instanceof DefinitionStmt){
            System.out.println("Start to fetch key!");

            DefinitionStmt definitionStmt = (DefinitionStmt)stmt;
            Value right = definitionStmt.getRightOp();
            if(right instanceof InvokeExpr){
                InvokeExpr invokeExpr = (InvokeExpr)right;
                SootMethod signMethod = invokeExpr.getMethod();
                System.out.println(signMethod.getSignature());
                Queue<SootMethod> signMethodQueue = new LinkedList<>();
                signMethodQueue.offer(signMethod);
                boolean keyFound = false;
                int count = 0;
                while((!keyFound) && (!signMethodQueue.isEmpty()) && (count < 5)){
                    SootMethod iterMethod = signMethodQueue.poll();
                    assert iterMethod != null;
                    Iterator stmts = iterMethod.retrieveActiveBody().getUnits().snapshotIterator();
                    while(stmts.hasNext()){
                        Stmt iterStmt = (Stmt)stmts.next();
                        System.out.println(iterStmt.toString());
                        if(iterStmt instanceof InvokeStmt){
                            InvokeStmt iterInvokeStmt = (InvokeStmt)iterStmt;
                            InvokeExpr iterInvokeExpr = iterInvokeStmt.getInvokeExpr();
                            if (iterInvokeExpr.getMethod().getSignature().equals("<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>")){
                                System.out.println("into append");
                                Value arg = iterInvokeExpr.getArg(0);
                                if(keyFound){
                                    return getItemValue(arg);
                                }
                                else{
                                    if (arg instanceof StringConstant){
                                        StringConstant stringConstant = (StringConstant)arg;
                                        if (stringConstant.toString().equals("\"key=\"")){
                                            keyFound = true;
                                            System.out.println("Key Found!");
                                        }
                                    }
                                }

                            }
                            else{
                                signMethodQueue.offer(iterInvokeExpr.getMethod());
                            }
                        }
                        else if(iterStmt instanceof DefinitionStmt){
                            DefinitionStmt iterDefinitionStmt = (DefinitionStmt)iterStmt;
                            Value iterRight = iterDefinitionStmt.getRightOp();
                            if(iterRight instanceof InvokeExpr){
                                InvokeExpr iterInvokeExpr = (InvokeExpr)iterRight;
                                signMethodQueue.offer(iterInvokeExpr.getMethod());
                            }
                        }
                    }
                    count = count + 1;

                }


            }


        }
        return null;
    }

    public static boolean checkGetPrePayIdHost(Value value){
        if (value instanceof InvokeExpr){
            InvokeExpr invokeExpr = (InvokeExpr)value;
            List<Value> invokeArgs = invokeExpr.getArgs();
            for (Value arg : invokeArgs) {
                if (arg instanceof StringConstant) {
                    StringConstant constant = (StringConstant) arg;
                    String notifyUrlStr = constant.toString();
//                    System.out.println(notifyUrlStr);
                    if (notifyUrlStr.equals("\"https://api.mch.weixin.qq.com/pay/unifiedorder\"")) {
                        System.out.println("find request prepayid url!");
                        System.out.println(notifyUrlStr);
                        return true;
                    }
                }
            }
        }
        else if(value instanceof StringConstant){
            StringConstant constant = (StringConstant)value;
            String notifyUrlStr = constant.toString();
//            System.out.println(notifyUrlStr);
            if(notifyUrlStr.equals("\"https://api.mch.weixin.qq.com/pay/unifiedorder\"")){
                System.out.println("find request prepayid url!");
                System.out.println(notifyUrlStr);
                return true;
            }
        }

        return false;
    }

    public static void main(String[] args){
        parseInputXML("/Users/ring/Documents/pwnzen/WX-Workspace/output/first/0a4de8e11298936ccbd73b1790cadac2.apk.xml");
        appPath = "/Users/ring/Documents/android-apks/127d78ee101de02a1e32efb198853b3606f822cd.apk";
        outputDir = "/Users/ring/Documents/output";
        System.out.println(appName);
        if (appName.endsWith(".apk")){
            Options.v().set_src_prec(Options.src_prec_apk);
        }

        LinkedList<String> processDir = new LinkedList<>();
        //System.out.println(appPath);
        //processDir.add(appPath);
        Options.v().set_whole_program(true);
        Options.v().set_process_dir(Collections.singletonList(appPath));
        Options.v().set_process_multiple_dex(true);
        Options.v().set_android_jars("/Users/ring/Documents/pwnzen/soot/android-platforms");
        Options.v().set_output_format(Options.output_format_jimple);
        Options.v().set_allow_phantom_refs(true);
        Options.v().set_ignore_resolution_errors(true);

        Scene.v().loadBasicClasses();

        ExecutorService executor = Executors.newSingleThreadExecutor();
        FutureTask<String> future = new FutureTask<>(new Callable<String>() {
            public String call() {
                try {
                    Iterator iterator = clazzMap.entrySet().iterator();
                    while (iterator.hasNext() && (!success)) {
                        Map.Entry pair = (Map.Entry) iterator.next();
                        String clazzName = (String) pair.getKey();
                        int type = (Integer) pair.getValue();
                        SootClass clazz = Scene.v().loadClassAndSupport(clazzName);
                        System.out.println(clazz.getName());
//                HashSet<String> prepayidReqMethodSet = new HashSet<String>();

//                int fieldType = 0x0001;

                        List<SootMethod> methods = clazz.getMethods();
                        for (SootMethod method : methods) {
//                    System.out.println(method.getSignature());
                            int modifier = method.getModifiers();
                            if (!Modifier.isInterface(modifier) && !Modifier.isAbstract(modifier)) {
                                Iterator stmts = method.retrieveActiveBody().getUnits().snapshotIterator();
                                while (stmts.hasNext()) {
                                    Stmt stmt = (Stmt) stmts.next();
//                            System.out.println(stmt.toString());
                                    boolean isGetPrePayIdHost = false;
                                    if (stmt instanceof InvokeStmt) {
                                        InvokeStmt invokeStmt = (InvokeStmt) stmt;
                                        InvokeExpr invokeExpr = invokeStmt.getInvokeExpr();
                                        isGetPrePayIdHost = checkGetPrePayIdHost(invokeExpr);
                                    } else if (stmt instanceof ReturnStmt) {
                                        ReturnStmt returnStmt = (ReturnStmt) stmt;
                                        Value returnArg = returnStmt.getOp();
                                        isGetPrePayIdHost = checkGetPrePayIdHost(returnArg);

                                    } else if (stmt instanceof DefinitionStmt) {
                                        DefinitionStmt definitionStmt = (DefinitionStmt) stmt;
                                        Value definitionArg = definitionStmt.getRightOp();
                                        isGetPrePayIdHost = checkGetPrePayIdHost(definitionArg);
                                    }
                                    if (isGetPrePayIdHost) {
                                        success = fromPrePayIdHostToPutArg(method);
                                        if (success) {
                                            break;
                                        }
                                    }
                                }
                                if (success) {
                                    break;
                                }
                            }
                        }
                    }

                    if (success) {
                        DocumentBuilderFactory dbFactory = DocumentBuilderFactory.newInstance();
                        DocumentBuilder dBuilder = dbFactory.newDocumentBuilder();
                        Document doc = dBuilder.newDocument();
                        Element rootElement = doc.createElement("app");
                        doc.appendChild(rootElement);
                        Element appNameElement = doc.createElement("name");
                        appNameElement.appendChild(doc.createTextNode(appName));
                        rootElement.appendChild(appNameElement);
                        Element appPathElement = doc.createElement("path");
                        appPathElement.appendChild(doc.createTextNode(appPath));
                        rootElement.appendChild(appPathElement);

                        Element appidElement = doc.createElement("appid");
                        if (appid != null) {
                            appidElement.appendChild(doc.createTextNode(appid.substring(1, appid.length() - 1)));
                        } else {
                            appidElement.appendChild(doc.createTextNode(""));
                        }
                        rootElement.appendChild(appidElement);

                        Element mch_idElement = doc.createElement("mch_id");
                        if (mch_id != null) {
                            mch_idElement.appendChild(doc.createTextNode(mch_id.substring(1, mch_id.length() - 1)));
                        } else {
                            mch_idElement.appendChild(doc.createTextNode(""));
                        }
                        rootElement.appendChild(mch_idElement);

                        Element notify_urlElement = doc.createElement("notify_url");
                        if (notify_url != null) {
                            notify_urlElement.appendChild(doc.createTextNode(notify_url.substring(1, notify_url.length() - 1)));
                        } else {
                            notify_urlElement.appendChild(doc.createTextNode(""));
                        }
                        rootElement.appendChild(notify_urlElement);

                        Element keyElement = doc.createElement("key");
                        if (key != null) {
                            keyElement.appendChild(doc.createTextNode(key.substring(1, key.length() - 1)));
                        } else {
                            keyElement.appendChild(doc.createTextNode(""));
                        }
                        rootElement.appendChild(keyElement);


                        /*
                        TransformerFactory transformerFactory = TransformerFactory.newInstance();
                        Transformer transformer = transformerFactory.newTransformer();
                        DOMSource domSource = new DOMSource(doc);
                        StreamResult streamResult = new StreamResult(new File(outputDir + "/" + appName + "-result.xml"));
                        transformer.transform(domSource, streamResult);
                        */
                    }
                } catch (Exception e) {
                    e.printStackTrace();
                }
                return null;
            }
        });
        executor.execute(future);
        try {
            String result = future.get(10000000, TimeUnit.MILLISECONDS);
        } catch (InterruptedException | ExecutionException | TimeoutException e) {
            e.printStackTrace();
            future.cancel(true);
        } finally {
            executor.shutdown();
        }

    }


}
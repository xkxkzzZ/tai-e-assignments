/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
//        AddReachable(c : m)
//            if c : m ∉ RM then
//                add c : m to RM
//                S ∪= S_m
//                foreach i : x = new T() ∈ S_m do  // new
//                    add ⟨c : x, {c : o_i}⟩ to WL
//                foreach x = y ∈ S_m do        // copy
//                    AddEdge(c : y, c : x)
//                ... [ static store, load and invoke ]
//
//        S: Set of reachable statements
//        Sm: Set of statements in method m
//        RM: Set of reachable methods

        if (callGraph.addReachableMethod(csMethod)) {
            csMethod.getMethod().getIR().getStmts().forEach(stmt -> {
                stmt.accept(new StmtProcessor(csMethod));
            });
        }

    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        public Void visit(New stmt){ // new:   x = new T()
            //add ⟨c : x, {c : o_i}⟩ to WL
            Var var = stmt.getLValue();     // x
            CSVar csvar = csManager.getCSVar(context, var);  // c : x
            Obj obj = heapModel.getObj(stmt);   // o_i
            Context c1 = contextSelector.selectHeapContext(csMethod, obj);
            CSObj csobj = csManager.getCSObj(c1, obj); // c1 : o_i
            PointsToSet pointsToSet = PointsToSetFactory.make(csobj); // {c : o_i}
            workList.addEntry(csvar, pointsToSet);
            return null;
        }
        public Void visit(Copy stmt){ // copy: x = y
            //AddEdge(c : y, c : x)
            Pointer source = csManager.getCSVar(context, stmt.getRValue());
            Pointer target = csManager.getCSVar(context, stmt.getLValue());
            addPFGEdge(source, target);
            return null;
        }
        public Void visit(StoreField stmt){ // static store
            if (stmt.isStatic()){ //T.f = y
                // AddEdge(c:y, T.f)
                JField field = stmt.getFieldRef().resolve(); // f
                Pointer source = csManager.getCSVar(context, stmt.getRValue()); // c : y
                Pointer target = csManager.getStaticField(field); // T.f
                addPFGEdge(source, target);
            }
            return null;
        }
        public Void visit(LoadField stmt){ // static load
            if (stmt.isStatic()){ // y = T.f
                // AddEdge(T.f, c : y)
                JField field = stmt.getFieldRef().resolve(); // f
                Pointer source = csManager.getStaticField(field); // T.f
                Pointer target = csManager.getCSVar(context, stmt.getLValue()); // c : x
                addPFGEdge(source, target);
            }
            return null;
        }
        public Void visit(Invoke stmt){ // Static invoke
            if (stmt.isStatic()){
                CSCallSite cscallsite = csManager.getCSCallSite(context, stmt);
                JMethod m = CallGraphs.resolveCallee(null, stmt);
                Context ct = contextSelector.selectContext(cscallsite, m);
                CSMethod csmethod = csManager.getCSMethod(ct, m);
                HandleInvoke(cscallsite, csmethod);
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
//        Exactly same as in C.I. analysis
//        AddEdge(s, t)
//            if s → t ∉ PFG then
//                add s → t to PFG
//                if pt(s) is not empty then
//                    add ⟨t, pt(s)⟩ to WL

        if (pointerFlowGraph.addEdge(source, target)) {
            PointsToSet pointsToSet = source.getPointsToSet();
            if (pointsToSet != null) {
                workList.addEntry(target, pointsToSet);
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
//        while WL is not empty do
//            remove ⟨n, pts⟩ from WL
//            Δ = pts − pt(n)
//            Propagate(n, Δ)
//            if n represents a variable c : x then
//                foreach c′ : o_i ∈ Δ do
//                    foreach x.f = y ∈ S do
//                        AddEdge(c : y, c′ : o_i.f)
//                    foreach y = x.f ∈ S do
//                        AddEdge(c′ : o_i.f, c : y)
//                        ... [array load/store]
//                    ProcessCall(c : x, c′ : o_i)

        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer pointer = entry.pointer();  // n
            PointsToSet pointsToSet = entry.pointsToSet();  // pts
            PointsToSet delta = propagate(pointer, pointsToSet);    // Δ
            if (pointer instanceof  CSVar) {
                CSVar csvar = (CSVar) pointer; // c : x
                Var x = csvar.getVar(); // x
                Context c = csvar.getContext(); // c
                for (CSObj obj : delta.getObjects()) {  // c' : o_i
                    for(StoreField storeField : x.getStoreFields()){ // x.f = y
                        // AddEdge(c : y, c′ : o_i.f)
                        Pointer source = csManager.getCSVar(c, storeField.getRValue()); // c : y
                        Pointer target = csManager.getInstanceField(obj, storeField.getFieldRef().resolve()); // c' : o_i.f
                        addPFGEdge(source, target);
                    }
                    for (LoadField loadField : x.getLoadFields()){ // y = x.f
                        // AddEdge(c′ : o_i.f, c : y)
                        Pointer source = csManager.getInstanceField(obj, loadField.getFieldRef().resolve()); // c' : o_i.f
                        Pointer target = csManager.getCSVar(c, loadField.getLValue()); // c : y
                        addPFGEdge(source, target);
                    }
                    for (StoreArray storeArray : x.getStoreArrays()){ // x[*] = y
                        // AddEdge(c : y, c′ : o_i[*])
                        Pointer source = csManager.getCSVar(c, storeArray.getRValue()); // c : y
                        Pointer target = csManager.getArrayIndex(obj); // c' : o_i[*]
                        addPFGEdge(source, target);
                    }
                    for (LoadArray loadArray : x.getLoadArrays()){ // y = x[*]
                        // AddEdge(c′ : o_i[*], c : y)
                        Pointer source = csManager.getArrayIndex(obj); // c' : o_i[*]
                        Pointer target = csManager.getCSVar(c, loadArray.getLValue()); // c : y
                        addPFGEdge(source, target);
                    }
                    processCall(csvar, obj);   // ProcessCall(c : x, c' : o_i)
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
//        Exactly same as in C.I. analysis
//        1.  Δ= pts – pt(n)
//        2.  Propagate(n, Δ)

//        Propagate(n, pts)
//        if pts is not empty then
//        pt(n) ∪= pts
//        foreach n → s ∈ PFG do
//            add ⟨s, pts⟩ to WL

        PointsToSet delta = PointsToSetFactory.make();
        for (CSObj obj : pointsToSet.getObjects()) {
            if (! pointer.getPointsToSet().contains(obj)) {
                delta.addObject(obj);
                pointer.getPointsToSet().addObject(obj);
                for (Pointer succ : pointerFlowGraph.getSuccsOf(pointer)) {
                    workList.addEntry(succ, pointsToSet);
                }
            }
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {   // recv - c : x, recvObj - c' : o_i
        // TODO - finish me
//        ProcessCall(c : x, c′ : o_i)
//            foreach l : r = x.k(a1, ..., an) ∈ S do
//                m = Dispatch(o_i, k)
//                c^t = Select(c, l, c′ : o_i)
//                add ⟨c^t : m_this, {c′ : o_i}⟩ to WL
//                if c : l → c^t : m ∉ CG then
//                    add c : l → c^t : m to CG
//                    AddReachable(c^t : m)
//                    foreach parameter p_i of m do
//                        AddEdge(c : a_i, c^t : p_i)
//                    AddEdge(c^t : m_ret, c : r)

        // foreach l : r = x.k(a1, ..., an) ∈ S do
        for (Invoke invoke : recv.getVar().getInvokes()) {  // invoke - l
            // m = Dispatch(o_i, k)
            JMethod m = resolveCallee(recvObj, invoke);

            // c^t = Select(c, l, c′ : o_i)
            Context c = recv.getContext();  // c
            CSCallSite cscallsite = csManager.getCSCallSite(c, invoke); // c : l
            Context ct = contextSelector.selectContext(cscallsite, recvObj, m); // c^t

            // add ⟨c^t : m_this, {c′ : o_i}⟩ to WL
            Pointer mThis = csManager.getCSVar(ct, m.getIR().getThis());    // c^t : m_this
            PointsToSet pointsToSet = PointsToSetFactory.make(recvObj);     // {c' : o_i}
            workList.addEntry(mThis, pointsToSet);

            CSMethod csmethod = csManager.getCSMethod(ct, m); // c^t : m
            HandleInvoke(cscallsite, csmethod);
        }
    }

    private void HandleInvoke(CSCallSite cscallsite, CSMethod csmethod) { // cscallsite - c : l, csmethod - c^t : m
//                if c : l → c^t : m ∉ CG then
//                    add c : l → c^t : m to CG
//                    AddReachable(c^t : m)
//                    foreach parameter p_i of m do
//                        AddEdge(c : a_i, c^t : p_i)
//                    AddEdge(c^t : m_ret, c : r)

        Invoke invoke = cscallsite.getCallSite(); // l
        Context c = cscallsite.getContext();    // c
        JMethod m = csmethod.getMethod();       // m
        Context ct = csmethod.getContext();     // c^t
        CallKind kind = CallGraphs.getCallKind(invoke);
        var calledge = new Edge<>(kind, cscallsite, csmethod);
        // add c : l → c^t : m to CG
        if (callGraph.addEdge(calledge)) {
            // AddReachable(c^t : m)
            addReachable(csmethod);
            // AddEdge(c : a_i, c^t : p_i)
            for (int i = 0; i < invoke.getInvokeExp().getArgCount(); i++) {
                Pointer source = csManager.getCSVar(c, invoke.getInvokeExp().getArg(i));
                Pointer target = csManager.getCSVar(ct, m.getIR().getParam(i));
                addPFGEdge(source, target);
            }
            // AddEdge(c^t : m_ret, c : r)
            Var r = invoke.getResult();
            if (r != null) {
                m.getIR().getReturnVars().forEach(mret -> {
                    Pointer source = csManager.getCSVar(ct, mret);
                    Pointer target = csManager.getCSVar(c, r);
                    addPFGEdge(source, target);
                });
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}

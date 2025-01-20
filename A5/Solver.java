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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
//        AddReachable(m)
//          if m ∉ RM then
//              add m to RM
//              S U= Sm
//              [visitor]:
//              foreach i: x = new T() ∈ Sm do // new
//                  add <x, {oi}> to WL
//              foreach x = y ∈ Sm do     // copy
//                  AddEdge(y, x)
//              ... [ static store, load and invoke ]
//
//        S: Set of reachable statements
//        Sm: Set of statements in method m
//        RM: Set of reachable methods

        if (callGraph.addReachableMethod(method)) {
            method.getIR().getStmts().forEach(stmt -> stmt.accept(stmtProcessor));
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        @Override
        public Void visit(New stmt) { // x = new T()
            // add <x, {oi}> to WL
            Pointer pointer = pointerFlowGraph.getVarPtr(stmt.getLValue()); // x
            // 堆抽象 heapModel - 创建点抽象，getObj为 New 语句返回一个唯一的抽象对象 oi
            PointsToSet pointsToSet = new PointsToSet(heapModel.getObj(stmt)); // {oi}
            workList.addEntry(pointer, pointsToSet);
            return null;
        }
        @Override
        public Void visit(Copy stmt) { // x = y
            //AddEdge(y, x)
            Pointer source = pointerFlowGraph.getVarPtr(stmt.getRValue());
            Pointer target = pointerFlowGraph.getVarPtr(stmt.getLValue());
            addPFGEdge(source, target);
            return null;
        }

        @Override
        public Void visit(StoreField stmt) { // Static Store
            if(stmt.isStatic()) {   // T.f = y
                // AddEdge (y, T.f)
                JField field = stmt.getFieldRef().resolve();
                Pointer source = pointerFlowGraph.getVarPtr(stmt.getRValue());
                Pointer target = pointerFlowGraph.getStaticField(field);
                addPFGEdge(source, target);
            }
            return null;
        }
        @Override
        public Void visit(LoadField stmt) {  // Static Load
            if(stmt.isStatic()) {   // y = T.f
                // AddEdge (T.f, y)
                JField field = stmt.getFieldRef().resolve();
                Pointer source = pointerFlowGraph.getStaticField(field);
                Pointer target = pointerFlowGraph.getVarPtr(stmt.getLValue());
                addPFGEdge(source, target);
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {   // Static invoke
            if (stmt.isStatic()) {  // r = T.m(a1,...,an)
                JMethod m = stmt.getMethodRef().resolve();
                HandleInvoke(m, stmt);
            }
            return null;
        }

    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
//        AddEdge(s, t)
//          if s → t ∉ PFG then
//              add s → t to PFG
//              if pt(s) is not empty then
//                  add <t, pt(s)> to WL
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
//          remove <n, pts> from WL
//          Δ= pts –pt(n)
//          Propagate(n, Δ)
//          if n represents a variable x then
//              foreach oi ∈ Δ do
//                  foreach x.f= y ∈ S do   // non-static store field
//                      AddEdge(y, oi.f)
    //              foreach y = x.f ∈ S do  // non-static load field
    //                  AddEdge(oi.f, y)
    //              ... [array]
    //              ProcessCall(x, oi)

//        提示：不要忘记在这个方法中处理数组 loads/stores。

        while (! workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer pointer = entry.pointer();  // n
            PointsToSet pointsToSet = entry.pointsToSet();  // pts
            PointsToSet delta = propagate(pointer, pointsToSet); // Δ

            if(pointer instanceof VarPtr){
                Var var = ((VarPtr) pointer).getVar(); // x
                for (Obj obj : delta) {  // oi
                    for(StoreField storeField: var.getStoreFields()){  // x.f = y
                        // AddEdge(y, oi.f)
                        Pointer source = pointerFlowGraph.getVarPtr(storeField.getRValue());  // y
                        Pointer target = pointerFlowGraph.getInstanceField(obj, storeField.getFieldRef().resolve());  // oi.f
                        addPFGEdge(source, target);
                    }
                    for(LoadField loadField: var.getLoadFields()){  // y = x.f
                        // AddEdge(oi.f, y)
                        Pointer source = pointerFlowGraph.getInstanceField(obj, loadField.getFieldRef().resolve());  // oi.f
                        Pointer target = pointerFlowGraph.getVarPtr(loadField.getLValue());  // y
                        addPFGEdge(source, target);
                    }
                    for(StoreArray storeArray: var.getStoreArrays()){  // x[*] = y
                        // AddEdge(y, oi[*])
                        Pointer source = pointerFlowGraph.getVarPtr(storeArray.getRValue());  // y
                        Pointer target = pointerFlowGraph.getArrayIndex(obj);  // oi[*]
                        addPFGEdge(source, target);
                    }
                    for(LoadArray loadArray: var.getLoadArrays()){  // y = x[*]
                        // AddEdge(oi[*], y)
                        Pointer source = pointerFlowGraph.getArrayIndex(obj);  // oi[*]
                        Pointer target = pointerFlowGraph.getVarPtr(loadArray.getLValue());  // y
                        addPFGEdge(source, target);
                    }
                    processCall(var, obj);
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
//        这个方法合并了算法中的两个步骤
//        它首先计算差集Δ= pts – pt(n)，然后将 pts 传播到 pt(p) 中。它返回 Δ 作为调用的结果。
//        1.  Δ= pts – pt(n)
//        2.  Propagate(n, Δ)

//        Propagate(n, pts)
//          if pts is not empty then
//              pt(n) ⋃= pts
//              foreach n → s ∈ PFG do
//                add <s, pts> to WL

        PointsToSet delta = new PointsToSet();
        for (Obj obj : pointsToSet) {
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
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
//        ProcessCall(x, oi)
//            foreach l: r = x.k(a1,…,an) ∈ S do
//                m = Dispatch(oi, k)
//                add <m_this, {oi}> to WL
//                if l → m ∉ CG then
//                  add l → m to CG
//                  AddReachable(m)
//                  for each parameter pi                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                of 𝑚𝑚do
//                      AddEdge(ai, pi)
//                  AddEdge(m_ret, r)

        for (Invoke callSite : var.getInvokes()) {  // r = x.k(a1,...,an)
            JMethod m = resolveCallee(recv, callSite); // m = Dispatch(oi, k)
            // add <m_this, {oi}> to WL
            Pointer mThis = pointerFlowGraph.getVarPtr(m.getIR().getThis());
            PointsToSet pointsToSet = new PointsToSet(recv);
            workList.addEntry(mThis, pointsToSet);
            HandleInvoke(m, callSite);
        }
    }

    private void HandleInvoke(JMethod m, Invoke callSite) {
        CallKind kind = null;
        if (callSite.isStatic()) {
            kind = CallKind.STATIC;
        } else if (callSite.isVirtual()) {
            kind = CallKind.VIRTUAL;
        } else if (callSite.isDynamic()) {
            kind = CallKind.DYNAMIC;
        } else if (callSite.isInterface()) {
            kind = CallKind.INTERFACE;
        } else if (callSite.isSpecial()) {
            kind = CallKind.SPECIAL;
        }

        //add l → m to CG
        if (kind != null && callGraph.addEdge(new Edge<>(kind, callSite, m))) {
            // AddReachable(m)
            addReachable(m);

            // AddEdge(ai, pi)
            for (int i = 0; i < callSite.getInvokeExp().getArgCount(); i++) {
                Pointer source = pointerFlowGraph.getVarPtr(callSite.getInvokeExp().getArg(i));  // ai
                Pointer target = pointerFlowGraph.getVarPtr(m.getIR().getParam(i));  // pi
                addPFGEdge(source, target);
            }
            // AddEdge(m_ret, r)
            Var r = callSite.getResult();
            if (r != null) {
                m.getIR().getReturnVars().forEach(mret -> {
                    Pointer source = pointerFlowGraph.getVarPtr(mret);  // m_ret
                    Pointer target = pointerFlowGraph.getVarPtr(r);  // r
                    addPFGEdge(source, target);
                });
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}

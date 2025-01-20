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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.cs.Solver;

import java.util.Set;
import java.util.TreeSet;


import pascal.taie.analysis.graph.callgraph.CallGraph;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Pair;
import java.util.*;




public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
    }

    // TODO - finish me
//    污点传播 Taint Transfer :
//    告诉污点分析哪些方法会引发污点传播以及它们是如何传播污点的。
//    在这次作业中，当一个引发污点传播的方法 foo 被调用时，有以下三种污点传播的模式：
    public Set<Pair<Var, Obj>> TaintTransfer(CSCallSite csCallSite, JMethod callee, CSVar base){
        // c:l -> ct:m in CG
        // l = x.k(a1, ..., an)
        Invoke callSite = csCallSite.getCallSite();
        Var lVar = callSite.getLValue();
        PointerAnalysisResult ptaResult = solver.getResult();
        Set<Pair<Var, Obj>> result = new HashSet<>();
        TaintTransfer transfer;
        // <m, form, to, u>
        //其中 m 表示会引发污点传播的方法，
        //而污点会从 from 所表示的变量中传播到 to 所表示的变量中。
        // u表示传播后的污点（由 to 指向）的类型。
        // from: index of parameter/ “base”
        // to: "base" / "result"
        if(base != null) {
            // Call (base-to-result)
//            Base-to-result：如果 receiver object（由 base 指向）被污染了，
//            那么该方法调用的返回值也会被污染。
//            StringBuilder.toString() 是这样一类方法。
            Type resultType = callee.getReturnType();
            transfer = new TaintTransfer(callee, TaintTransfer.BASE, TaintTransfer.RESULT, resultType);
            if(config.getTransfers().contains(transfer) && lVar != null){
                // (m, base, result, u) in TaintTransfer
                Set<CSObj> basePts = ptaResult.getPointsToSet(base);
                basePts.forEach(csObj -> {
                    if(manager.isTaint(csObj.getObject())){
                        // []:taint(j, u‘) in pt(c:base)
                        Obj taint = manager.makeTaint(manager.getSourceCall(csObj.getObject()), resultType);
                        // add []:taint(j, u) in pt(c:result)
                        result.add(new Pair<>(lVar, taint));
                    }
                });
            }
            // Call (arg-to-base)
//            Arg-to-base：如果某个特定的参数被污染了，
//            那么 receiver object（由 base 指向）也会被污染。
//            StringBuilder.append(String) 是这样一类方法。
            Type baseType = base.getType();
            List<Var> args = callSite.getInvokeExp().getArgs();
            for (int i = 0; i < args.size(); i++) {
                Var arg = args.get(i);
                Set<CSObj> argPts = ptaResult.getPointsToSet(csManager.getCSVar(csCallSite.getContext(), arg));
                transfer = new TaintTransfer(callee, i, TaintTransfer.BASE, baseType);
                if (config.getTransfers().contains(transfer)) {
                    // (m, i, base, u) in TaintTransfer
                    argPts.forEach(csObj -> {
                        if(manager.isTaint(csObj.getObject())){
                            // []:taint(j, u‘) in pt(c:ai)
                            Obj taint = manager.makeTaint(manager.getSourceCall(csObj.getObject()), baseType);
                            // add []:taint(j, u) in pt(c:base)
                            result.add(new Pair<>(base.getVar(), taint));
                        }
                    });
                }
            }
        }
//        因为静态方法没有 base 变量，所以他们不会引起 base-to-result 和 arg-to-base 的污点传播。

        // Call (arg-to-result)
//        Arg-to-result：如果某个特定的参数被污染了，
//        那么该方法调用的返回值也会被污染。
//        String.concat(String) 是这样一类方法。
        List<Var> args = callSite.getInvokeExp().getArgs();
        Type resultType = callee.getReturnType();
        for (int i = 0; i < args.size(); i++) {
            Var arg = args.get(i);
            Set<CSObj> argPts = ptaResult.getPointsToSet(csManager.getCSVar(csCallSite.getContext(), arg));
            transfer = new TaintTransfer(callee, i, TaintTransfer.RESULT, resultType);
            if (config.getTransfers().contains(transfer)) {
                // (m, i, result, u) in TaintTransfer
                argPts.forEach(csObj -> {
                    if(manager.isTaint(csObj.getObject())){
                        // []:taint(j, u‘) in pt(c:ai)
                        Obj taint = manager.makeTaint(manager.getSourceCall(csObj.getObject()), resultType);
                        // add []:taint(j, u) in pt(c:result)
                        result.add(new Pair<>(lVar, taint));
                    }
                });
            }
        }
        return result;
    }

    public boolean isTaint(Obj obj){
        return manager.isTaint(obj);
    }

    // Call (source)
    // l: r = x.k(a1, ..., an)
    // Rules:
    // c: l-> ct:m in CG
    // (m, u) in sources
    //  ==>   taint(l, u) in pt(c:r)
    public Obj callSource(Invoke callSite, JMethod callee){ // l, m
        Type type = callee.getReturnType(); // u
        if(config.getSources().contains(new Source(callee, type))){ // if (m, u) in sources
            return manager.makeTaint(callSite, type);  // taint(l, u)
        }
        return null;
    }

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // TODO - finish me
        // You could query pointer analysis results you need via variable result.
        CallGraph<CSCallSite, CSMethod> callGraph = result.getCSCallGraph();
        callGraph.reachableMethods().forEach(csMethod -> {
            callGraph.getCallersOf(csMethod).forEach(csCallSite -> {
                Invoke callSite = csCallSite.getCallSite(); // l
                JMethod method = csMethod.getMethod(); // m
                List<Var> args = callSite.getInvokeExp().getArgs(); // a1, ..., an
                // call (sink)
                // l: r = x.k(a1, ..., an)
                // Rules:
                // c: l-> ct:m in CG
                // (m, i) in sinks
                // []:t(j, u) in pt(c:ai)
                //  ==>   (j, l, i) in taintFlows
                for(int i = 0;i < args.size();i ++){
                    Var arg = args.get(i); // ai
                    if(config.getSinks().contains(new Sink(method, i))){ // if (m, i) in sinks
                        for(Obj obj : result.getPointsToSet(arg)){ // for t in pt(c:ai)
                            if(manager.isTaint(obj)){ // if []:t(j, u) in pt(c:ai)
                                TaintFlow taintFlow = new TaintFlow(manager.getSourceCall(obj), callSite, i); // (j, l, i)
                                taintFlows.add(taintFlow); // add (j, l, i) in taintFlows
                            }
                        }
                    }
                }
            });
        });
        return taintFlows;
    }
}

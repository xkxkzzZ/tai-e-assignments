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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;


/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me
        // WL work list, CG call graph, RM reachable methods

        // BuildCallGraph(m^entry)
        // WL = [m^entry], CG = {}, RM = {}
        // while WL is not empty do
        //    remove m from WL
        //    if m is not in RM then
        //        add m to RM
        //        foreach cs in m do
        //            T = Resolve(cs)
        //            foreach target method m′ in T do
        //                add (cs, m′) to CG
        //                add m′ to WL
        // return CG

        Queue<JMethod> workList = new ArrayDeque<>();
        workList.add(entry);
        while (!workList.isEmpty()) {
            JMethod m = workList.poll();
            if (callGraph.addReachableMethod(m)) {
                m.getIR().forEach(stmt -> {
                    if (stmt instanceof Invoke callSite) {
                        CallKind kind = CallGraphs.getCallKind(callSite);
                        Set<JMethod> T = resolve(callSite);
                        T.forEach(mPrime -> {
                            callGraph.addEdge(new Edge<>(kind, callSite, mPrime));
                            workList.add(mPrime);
                        });
                    }
                });
            }
        }
        return callGraph;


    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me

//        Resolve(cs)
//        T = {}
//        m= method signature at cs
//        if cs is a static call then
//              T= { m }
//        if cs is special call then
//              c^m = class type of m
//              T= { Dispatch(c^m, m) }
//        if cs is a virtual call then
//            c = declared type of receiver variable at cs
//            foreach c′that is a subclass of c or c itself do
//                add Dispatch( c′,m) to T
//        return T
//
//
        Set T = new HashSet();
        MethodRef methodRef = callSite.getMethodRef();
        JClass jclass = methodRef.getDeclaringClass();
        Subsignature subsignature = methodRef.getSubsignature();
        JMethod m = jclass.getDeclaredMethod(subsignature);


        switch (CallGraphs.getCallKind(callSite)) {
            case STATIC:
                T.add(m);
                break;
            case SPECIAL:
                JMethod dispatchedMethod = dispatch(jclass, subsignature);
                if (dispatchedMethod != null) {
                    T.add(dispatchedMethod);
                }
                break;
            case VIRTUAL:
            case INTERFACE:
                Queue<JClass> queue = new ArrayDeque<>();
                queue.add(jclass);
                while (!queue.isEmpty()) {
                    JClass cPrime = queue.poll();
                    JMethod dispatched = dispatch(cPrime, subsignature);
                    if (dispatched != null) {
                        T.add(dispatched);
                    }
                    if(cPrime.isInterface()){
                        hierarchy.getDirectSubinterfacesOf(cPrime).forEach(queue::add);
                        hierarchy.getDirectImplementorsOf(cPrime).forEach(queue::add);
                    }
                    else{
                        hierarchy.getDirectSubclassesOf(cPrime).forEach(queue::add);
                    }
                }
                break;
        }
        return T;

    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        // Dispatch(c, m)
        // = m' if c contains m',if c contains non-abstract method m that
        //                          has the same name and descriptor as m
        // = Dispatch(c', m), otherwise: where c' is the superclass of c.

        JMethod m = jclass.getDeclaredMethod(subsignature);
        if (m != null && !m.isAbstract()) {
            return m;
        } else if (jclass.getSuperClass() == null) {
            return null;
        }
        return dispatch(jclass.getSuperClass(), subsignature);

    }
}

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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.util.collection.SetQueue;

import java.util.ArrayList;
import java.util.List;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    private void initialize() {
        // TODO - finish me
        //在初始化的过程中，过程间求解器需要初始化程序中所有的 IN/OUT fact，也就是 ICFG 的全部节点。
        // 但你仅需要对 ICFG 的 entry 方法（比如 main 方法）的 entry 节点设置 boundary fact。
        // 这意味着其他方法的 entry 节点和非 entry 节点的初始 fact 是一样的。
        Set<Node> entryNodes = icfg.entryMethods()
                .map(icfg::getEntryOf)
                .collect(Collectors.toSet());
        for (Node node : icfg.getNodes()) {
            if (entryNodes.contains(node)) {
                result.setInFact(node, analysis.newBoundaryFact(node));
                result.setOutFact(node, analysis.newBoundaryFact(node));
            } else {
                result.setInFact(node, analysis.newInitialFact());
                result.setOutFact(node, analysis.newInitialFact());
            }
        }
    }

    private void doSolve() {
        // TODO - finish me
        // 在计算一个节点的 IN fact 时，过程间求解器需要对
        // 传入的 edge 和前驱们的 OUT facts 应用 edge transfer 函数（transferEdge）。

        workList = new SetQueue<>();
        workList.addAll(icfg.getNodes());

        while (!workList.isEmpty()) {
            Node node = workList.poll();
            Fact inFact = analysis.newInitialFact();
            icfg.getInEdgesOf(node).forEach(edge -> {
                Fact edgeFact = analysis.transferEdge(edge, result.getOutFact(edge.getSource()));
                analysis.meetInto(edgeFact, inFact);
            });
            result.setInFact(node, inFact);

            Fact outFact = result.getOutFact(node);
            boolean changed = analysis.transferNode(node, inFact, outFact);
            result.setOutFact(node, outFact);

            if (changed) {
                workList.addAll(icfg.getSuccsOf(node));
            }
        }
    }
}

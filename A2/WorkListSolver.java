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

 package pascal.taie.analysis.dataflow.solver;

 import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
 import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
 import pascal.taie.analysis.dataflow.fact.DataflowResult;
 import pascal.taie.analysis.graph.cfg.CFG;
 
 import java.util.ArrayList;
 import java.util.LinkedList;
 import java.util.Queue;
 
 class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {
 
     WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
         super(analysis);
     }
 
     @Override
     protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
         // TODO - finish me
 
 //        Worklist ← all basic blocks
 //        while (Worklist is not empty)
 //        Pick a basic block B from Worklist
 //                old_OUT = OUT[B]
 //        IN[B] = ⊔Papredecessor of B OUT[P];
 //        OUT[B] = genB U (IN[B]- killB);
 //        if (old_OUT ≠ OUT[B])
 //        Add all successors of B to Worklist
 
         ArrayList<Node> worklist = new ArrayList<>();
 
         for (Node node : cfg) {
             if (!cfg.isEntry(node)) {
                 worklist.add(node);
             }
         }
 
         while (!worklist.isEmpty()) {
             Node node = worklist.remove(0);
             Fact inFact = analysis.newInitialFact();
             for (Node pred : cfg.getPredsOf(node)) {
                 analysis.meetInto(result.getOutFact(pred), inFact);
             }
             result.setInFact(node, inFact);
 
             Fact outFact = result.getOutFact(node);
             boolean changed = analysis.transferNode(node, inFact, outFact);
             result.setOutFact(node, outFact);
 
             if (changed){
                 for (Node succ : cfg.getSuccsOf(node)) {
                     if (!worklist.contains(succ)) {
                         worklist.add(succ);
                     }
                 }
             }
         }
     }
 
     @Override
     protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
         throw new UnsupportedOperationException();
     }
 }
 
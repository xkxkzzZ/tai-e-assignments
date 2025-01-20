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

import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;

import java.util.Collection;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        return out.copyFrom(in);
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        return cp.transferNode(stmt, in, out);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        // 这种边一般是与过程间调用无关的边，edge transfer 函数不需要对此进行特殊的处理。这种边上的 fact 经 transfer edge 之后不会有任何改变。
        // 换句话说，此时 edge transfer 是一个恒等函数，即 transferEdge(edge, fact) = fact。
        return out.copy();
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        // 对于方法调用 x = m(…)，edge transfer 函数会把等号左侧的变量（在这个例子里也就是 x）和它的值从 fact 中kill 掉。
        // 而对于等号左侧没有变量的调用，比如 m(…)，edge transfer 函数的处理方式与对待 normal edge 的一致：不修改 fact，edge transfer 是一个恒等函数。
        CPFact copy_out = out.copy();
        Stmt src = edge.getSource();
        if (src instanceof Invoke invoke) {
            Var result = invoke.getResult();
            if (result != null) {
                copy_out.remove(result);
            }
        }
        return copy_out;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        //对于这种边，edge transfer 函数会将实参（argument）在调用点中的值传递给被调用函数的形参（parameter）。
        // 具体来说，edge transfer 首先从调用点的 OUT fact 中获取实参的值，然后返回一个新的 fact，这个 fact 把形参映射到它对应的实参的值。
        CPFact res = new CPFact();
        Stmt src = edge.getSource();
        Stmt tgt = edge.getTarget();
        if (src instanceof Invoke invoke) {
            IR ir = icfg.getContainingMethodOf(tgt).getIR();
            for (int i = 0; i < ir.getParams().size(); i++) {
                Var param = ir.getParam(i);
                Var arg = invoke.getRValue().getArg(i);
                if (arg != null) {
                    res.update(param, callSiteOut.get(arg));
                }
            }
        }
        return res;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        // edge transfer 函数将被调用方法的返回值传递给调用点等号左侧的变量。
        // 具体来说，它从被调用方法的 exit 节点的 OUT fact 中获取返回值（可能有多个，你需要思考一下该怎么处理），
        // 然后返回一个将调用点等号左侧的变量映射到返回值的 fact。
        CPFact res = new CPFact();

        if (edge.getCallSite() instanceof Invoke invoke) {
            Var var = invoke.getResult();
            if (var != null) {
                Collection<Var> returns = edge.getReturnVars();
                Value v = Value.getUndef();
                for (Var ret : returns) {
                    v = cp.meetValue(v, returnOut.get(ret));
                }
                res.update(var, v);
            }
        }
        return res;
    }
}

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

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;

import pascal.taie.ir.stmt.*;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.language.classes.JField;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.analysis.pta.core.heap.Obj;
import java.util.*;


/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    private final HashMap<Var, Set<Var>> aliasMap;
    private final HashMap<JField, Set<LoadField>> staticLoadFields;
    private final HashMap<JField, Set<StoreField>> staticStoreFields;



    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
        aliasMap = new HashMap<>();
        staticLoadFields = new HashMap<>();
        staticStoreFields = new HashMap<>();
    }


    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        PointerAnalysisResult pta = World.get().getResult(ptaId);
        // You can do initialization work here

//        借助之前的作业中实现的指针分析来计算程序的别名信息。
//        具体而言，对任意两个实例字段的访问（设为 x.f 和 y.f），
//        如果它们的 base 变量的指针集（points-to set）有交集（即 x 和 y 的指针集有交集），
//        那么我们认为对这两个实例字段的访问（x.f 和 y.f）互为别名。

        for (Var x : pta.getVars()) {
            aliasMap.put(x, new HashSet<>());
            aliasMap.get(x).add(x);
            Set<Obj> xPts = pta.getPointsToSet(x);
            for (Var y : pta.getVars()) {
                if (x.equals(y)) {
                    continue;
                }
                Set<Obj> yPts = pta.getPointsToSet(y);
                if (!Collections.disjoint(xPts, yPts)) { // 有交集
                    aliasMap.get(x).add(y);
                }
            }
        }
        // load/store fields
        for (Stmt stmt: icfg) {
            if (stmt instanceof StoreField storeField && storeField.isStatic()) {
                JField field = storeField.getFieldRef().resolve();
                staticStoreFields.putIfAbsent(field, new HashSet<>());
                staticStoreFields.get(field).add(storeField);
            } else if (stmt instanceof LoadField loadField && loadField.isStatic()) {
                JField field = loadField.getFieldRef().resolve();
                staticLoadFields.putIfAbsent(field, new HashSet<>());
                staticLoadFields.get(field).add(loadField);
            }
        }

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
        // Actually changed in A7 - only here
        if (stmt instanceof LoadField loadField) {
            return handleLoadField(loadField, in, out);
        } else if (stmt instanceof StoreField storeField) {
            return handleStoreField(storeField, in, out);
        } else if (stmt instanceof LoadArray loadArray) {
            return handleArrayLoad(loadArray, in, out);
        } else if (stmt instanceof StoreArray storeArray) {
            return handleStoreArray(storeArray, in, out);
        } else {
            return cp.transferNode(stmt, in, out);
        }
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        // 与调用过程无关的边
        return out.copy();
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        // 方法调用
        // x = m(…) 把等号左侧的 x 从 fact 中 kill 掉
        // m(…) 当 normal edge 处理
        CPFact res = out.copy();
        if (edge.getSource() instanceof Invoke invoke) {
            Var result = invoke.getResult();
            if (result != null) {
                res.remove(result);
            }
        }
        return res;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        // 将实参（argument）在调用点中的值传递给被调用函数的形参（parameter）
        CPFact res = new CPFact();
        if (edge.getSource() instanceof Invoke invoke) {
            IR ir = edge.getCallee().getIR();
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
        // 将被调用方法的返回值传递给调用点等号左侧的变量
        CPFact res = new CPFact();

        if (edge.getCallSite() instanceof Invoke invoke) {
            Var lvar = invoke.getResult();
            if (lvar != null && ConstantPropagation.canHoldInt(lvar)) {
                Value retValue = Value.getUndef();
                for (Var ret : edge.getReturnVars()) {
                    retValue = cp.meetValue(retValue, returnOut.get(ret));
                }
                res.update(lvar, retValue);
            }
        }
        return res;
    }


    private boolean handleLoadField(LoadField loadField, CPFact in, CPFact out) {
//        当分析实例字段的 load 语句时（设该语句为 L），
//        我们找到所有对这一实例字段（以及其别名）进行修改的 store 语句，
//        并将这些语句要 store 的值 meet 之后赋给 L 等号左侧的变量，
        Var lValue = loadField.getLValue(); // x
        if (!ConstantPropagation.canHoldInt(lValue))
            return out.copyFrom(in);
        Value res = Value.getUndef();
        JField field = loadField.getFieldRef().resolve();  // a.f / T.f
        if (loadField.isStatic()) { // x = T.f
            // 静态字段，没有别名，只需 meet 所有 storeField 的 rvalue
            for (StoreField storeField : staticStoreFields.getOrDefault(field, new HashSet<>())) {
                //  所有的 T.f = __ 语句
                CPFact inFact = solver.getResult().getInFact(storeField);
                res = cp.meetValue(res, inFact.get(storeField.getRValue()));
            }
        } else { // x = a.f ( 有 p.f = y ，且 p.f 是 a.f 的别名 )
            Var base = ((InstanceFieldAccess) loadField.getFieldAccess()).getBase();
            for (Var alias : aliasMap.getOrDefault(base, new HashSet<>())) { // p, ..
                // 先找到所有别名，再 meet 所有 别名对应 field 的 store语句
                for (StoreField storeField : alias.getStoreFields()) { // for p.f = __, p.g = __
                    if (storeField.getFieldRef().resolve().equals(field)) { //对应的 p.f = __
                        CPFact inFact = solver.getResult().getInFact(storeField);
                        res = cp.meetValue(res, inFact.get(storeField.getRValue()));
                    }
                }
            }
        }
        CPFact copyIn = in.copy();
        copyIn.update(lValue, res); // x = res
        return out.copyFrom(copyIn);
    }

    private boolean handleStoreField(StoreField storeField, CPFact in, CPFact out) {
//        通过对一个字段/数组的访问来修改一个实例字段/数组将会同时修改与这一访问相关的所有别名值。
//        举例来说，如果 x.f，y.f 和 z.f 互为别名，那么 store 语句 x.f = 5;
//        不仅将 x.f 的值修改为 5，而且同时将 y.f 和 z.f 的值设为 5。
        Var rValue = storeField.getRValue();
        if (ConstantPropagation.canHoldInt(rValue)) {
            JField field = storeField.getFieldRef().resolve(); // x.f / T.f
            if (storeField.isStatic()) // T.f = 5
                staticLoadFields.getOrDefault(field, new HashSet<>()).forEach(solver::addWorkList);
            else { // x.f = 5
                Var base = ((InstanceFieldAccess) storeField.getFieldAccess()).getBase(); // x
                for (Var alias : aliasMap.getOrDefault(base, new HashSet<>())) { // y, z
                    for (LoadField loadField : alias.getLoadFields()) {
                        if (loadField.getFieldRef().resolve().equals(field))   // y.f, z.f
                            solver.addWorkList(loadField);
                    }
                }
            }
        }
        return out.copyFrom(in);
    }

    private boolean handleArrayLoad(LoadArray loadArray, CPFact in, CPFact out) {
        // x = a[i]
        Var lValue = loadArray.getLValue(); // x
        if (!ConstantPropagation.canHoldInt(lValue))
            return out.copyFrom(in);
        Value res = Value.getUndef();
        Var base = loadArray.getArrayAccess().getBase();  // a
        for (Var alias: aliasMap.getOrDefault(base, new HashSet<>())) { // 所有别名 b
            for (StoreArray storeArray : alias.getStoreArrays()) { // 别名的 store 语句 b[j] = __
                CPFact baseInFact = solver.getResult().getInFact(loadArray);
                Value i = baseInFact.get(loadArray.getArrayAccess().getIndex());
                CPFact aliasInFact = solver.getResult().getInFact(storeArray);
                Value j = aliasInFact.get(storeArray.getArrayAccess().getIndex());
                if (isAliasIndex(i, j)) // a[i] 和 b[j] 互为别名
                    res = cp.meetValue(res, aliasInFact.get(storeArray.getRValue()));
            }
        }
        CPFact copyIn = in.copy();
        copyIn.update(lValue, res); // x = res
        return out.copyFrom(copyIn);
    }
    private boolean isAliasIndex(Value x, Value y) {
//    根据常量传播中 i 和 j 的结果来决定 a[i] 和 b[j] 是否互为别名。具体参照如下表格
        if (x.isUndef() || y.isUndef())
            return false;
        if (x.isConstant() && y.isConstant())
            return x.equals(y);
        return true;
    }

    private boolean handleStoreArray(StoreArray storeArray, CPFact in, CPFact out) {
        // a[i] = x
        //通过对一个字段/数组的访问来修改一个实例字段/数组将会同时修改与这一访问相关的所有别名值。
        if (ConstantPropagation.canHoldInt(storeArray.getRValue())) {
            ArrayAccess arrAccess = storeArray.getArrayAccess();
            for (Var alias : aliasMap.getOrDefault(arrAccess.getBase(), new HashSet<>())) { // 所有别名
                alias.getLoadArrays().forEach(solver::addWorkList);
            }
        }
        return out.copyFrom(in);
    }
}
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

 package pascal.taie.analysis.dataflow.analysis.constprop;

 import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
 import pascal.taie.analysis.graph.cfg.CFG;
 import pascal.taie.config.AnalysisConfig;
 import pascal.taie.ir.exp.*;
 import pascal.taie.ir.stmt.DefinitionStmt;
 import pascal.taie.ir.stmt.Stmt;
 import pascal.taie.language.type.PrimitiveType;
 import pascal.taie.language.type.Type;
 
 import java.util.concurrent.atomic.AtomicBoolean;
 
 public class ConstantPropagation extends
         AbstractDataflowAnalysis<Stmt, CPFact> {
 
     public static final String ID = "constprop";
 
     public ConstantPropagation(AnalysisConfig config) {
         super(config);
     }
 
     @Override
     public boolean isForward() {
         return true;
     }
 
     @Override
     public CPFact newBoundaryFact(CFG<Stmt> cfg) {
         // TODO - finish me
         CPFact fact = new CPFact();
         cfg.getIR().getParams().forEach(var -> {
             if(canHoldInt(var)) {
                 fact.update(var, Value.getNAC());
             }
         });
         return fact;
     }
 
     @Override
     public CPFact newInitialFact() {
         // TODO - finish me
         return new CPFact();
     }
 
     @Override
     public void meetInto(CPFact fact, CPFact target) {
         // TODO - finish me
         fact.forEach((var, value) -> {
             Value newValue = meetValue(value, target.get(var));
             target.update(var, newValue);
         });
     }
 
     /**
      * Meets two Values.
      */
     public Value meetValue(Value v1, Value v2) {
         // TODO - finish me
 
         // NAC ⊓ v = NAC
         // UNDEF ⊓ v = v
         // c ⊓ c = c
         // c1 ⊓ c2 = NAC
 
         if(v1.isNAC() || v2.isNAC()) {
             return Value.getNAC();
         }
         if(v1.isUndef()) {
             return v2;
         }
         if(v2.isUndef()) {
             return v1;
         }
         if(v1.equals(v2)) {
             return v1;
         }
         return Value.getNAC();
 
     }
 
     @Override
     public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
         // TODO - finish me
 
         // OUT[s] = gen ∪ (IN[s]– {(x, _)})
 
         CPFact oldOut = out.copy();
         in.forEach(out::update);
 
         if(stmt instanceof DefinitionStmt) {
             DefinitionStmt defStmt = (DefinitionStmt) stmt;
             if(defStmt.getLValue() instanceof Var) {
                 Var var = (Var) defStmt.getLValue();
                 if(canHoldInt(var)) {
 
                     Value value = evaluate(defStmt.getRValue(), in);
                     out.update(var, value);
                 }
             }
         }
         boolean changed = !oldOut.equals(out);
         return changed;
     }
 
     /**
      * @return true if the given variable can hold integer value, otherwise false.
      */
     public static boolean canHoldInt(Var var) {
         Type type = var.getType();
         if (type instanceof PrimitiveType) {
             switch ((PrimitiveType) type) {
                 case BYTE:
                 case SHORT:
                 case INT:
                 case CHAR:
                 case BOOLEAN:
                     return true;
             }
         }
         return false;
     }
 
     /**
      * Evaluates the {@link Value} of given expression.
      *
      * @param exp the expression to be evaluated
      * @param in  IN fact of the statement
      * @return the resulting {@link Value}
      */
     public static Value evaluate(Exp exp, CPFact in) {
         // TODO - finish me
 
         // s: x = c;    gen = {(x, c)}
         // s: x = y;    gen = {(x, val(y))}
         // s: x = y op z;   gen = {(x, f(y,z))}
         // f(y,z) =  val(y) op val(z) // if val(y) and val(z) are constants
         //           NAC    // if val(y) or val(z) is NAC
         //           UNDEF  // otherwise
 
 
         if (exp instanceof IntLiteral) {
             return Value.makeConstant(((IntLiteral) exp).getValue());
         }
         else if (exp instanceof Var) {
             return in.get((Var) exp);
         }
         else if (exp instanceof BinaryExp) {
             BinaryExp binaryExp = (BinaryExp) exp;
             Var o1 = binaryExp.getOperand1();
             Var o2 = binaryExp.getOperand2();
             Value v1 = in.get(o1);
             Value v2 = in.get(o2);
 
             if (v1.isNAC() || v2.isNAC()) {
                 return Value.getNAC();
             }
             if (!(v1.isConstant()) || !(v2.isConstant())) {
                 return Value.getUndef();
             }
             // v1 and v2 are both constants
             int c1 = v1.getConstant();
             int c2 = v2.getConstant();
 
             if (exp instanceof ArithmeticExp){
                 ArithmeticExp.Op op = ((ArithmeticExp) exp).getOperator();
                 switch (op) {
                     case ADD:
                         return Value.makeConstant(c1 + c2);
                     case SUB:
                         return Value.makeConstant(c1 - c2);
                     case MUL:
                         return Value.makeConstant(c1 * c2);
                     case DIV:
                         if (c2 == 0) {
                             return Value.getUndef();
                         }
                         return Value.makeConstant(c1 / c2);
                     case REM:
                         if (c2 == 0) {
                             return Value.getUndef();
                         }
                         return Value.makeConstant(c1 % c2);
                 }
             }
             else if (exp instanceof BitwiseExp){
                 BitwiseExp.Op op = ((BitwiseExp) exp).getOperator();
                 switch (op) {
                     case AND:
                         return Value.makeConstant(c1 & c2);
                     case OR:
                         return Value.makeConstant(c1 | c2);
                     case XOR:
                         return Value.makeConstant(c1 ^ c2);
                 }
             }
             else if (exp instanceof ConditionExp){
                 ConditionExp.Op op = ((ConditionExp) exp).getOperator();
                 switch (op) {
                     case EQ:
                         return Value.makeConstant(c1 == c2 ? 1 : 0);
                     case NE:
                         return Value.makeConstant(c1 != c2 ? 1 : 0);
                     case LT:
                         return Value.makeConstant(c1 < c2 ? 1 : 0);
                     case LE:
                         return Value.makeConstant(c1 <= c2 ? 1 : 0);
                     case GT:
                         return Value.makeConstant(c1 > c2 ? 1 : 0);
                     case GE:
                         return Value.makeConstant(c1 >= c2 ? 1 : 0);
                 }
             }
             else if (exp instanceof ShiftExp){
                 ShiftExp.Op op = ((ShiftExp) exp).getOperator();
                 switch (op) {
                     case SHL:
                         return Value.makeConstant(c1 << c2);
                     case SHR:
                         return Value.makeConstant(c1 >> c2);
                     case USHR:
                         return Value.makeConstant(c1 >>> c2);
                 }
             }
         }
         return Value.getNAC();
     }
 }
 
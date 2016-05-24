package com.ipandora.core.function;

import com.ipandora.api.predicate.function.Function;
import com.ipandora.api.predicate.function.FunctionCase;
import com.ipandora.api.predicate.function.MathematicalFunction;
import com.ipandora.api.predicate.term.Term;
import com.ipandora.api.predicate.term.Type;
import com.ipandora.api.predicate.term.TypeMismatchException;
import com.ipandora.core.formula.FormulaTypeChecker;
import com.ipandora.core.term.TermTypeChecker;
import com.ipandora.core.util.WrappingRuntimeException;

public class FunctionTypeChecker {

    private final TermTypeChecker termTypeChecker;
    private final FormulaTypeChecker formulaTypeChecker;

    public FunctionTypeChecker(TermTypeChecker termTypeChecker, FormulaTypeChecker formulaTypeChecker) {
        this.termTypeChecker = termTypeChecker;
        this.formulaTypeChecker = formulaTypeChecker;
    }

    public void analyse(Function function) throws TypeMismatchException {
        try {
            function.accept(new FunctionTypeCheckingVisitor());
        } catch (WrappingRuntimeException wre) {
            Exception wrapped = wre.getWrappedException();
            if (wrapped instanceof TypeMismatchException) {
                throw (TypeMismatchException) wrapped;
            }
            throw wre;
        }
    }

    private class FunctionTypeCheckingVisitor implements FunctionVisitor<Void> {

        @Override
        public Void visit(Function function) {
            return function.accept(this);
        }

        @Override
        public Void visitMathematicalFunction(MathematicalFunction mathematicalFunction) {

            for (FunctionCase functionCase : mathematicalFunction.getCases()) {
                try {
                    Term expression = functionCase.getExpression();
                    if (expression.getType() != Type.NAT) {
                        throw new TypeMismatchException("Return expression not of type Nat: " + expression);
                    }

                    termTypeChecker.analyse(expression);
                    formulaTypeChecker.analyse(functionCase.getCondition().getFormula());
                } catch (TypeMismatchException e) {
                    throw new WrappingRuntimeException(e);
                }
            }

            return null;
        }
    }

}

package com.ipandora.core.function;

import com.ipandora.api.predicate.function.FunctionCase;
import com.ipandora.api.predicate.function.FunctionDefinition;
import com.ipandora.api.predicate.function.FunctionPrototype;
import com.ipandora.api.predicate.function.MathematicalFunctionDefinition;
import com.ipandora.api.predicate.term.Term;
import com.ipandora.api.predicate.term.TypeMismatchException;
import com.ipandora.core.formula.FormulaTypeChecker;
import com.ipandora.core.term.TermTypeChecker;
import com.ipandora.core.util.WrappingRuntimeException;

import java.util.List;

public class FunctionTypeChecker {

    private final TermTypeChecker termTypeChecker;
    private final FormulaTypeChecker formulaTypeChecker;

    public FunctionTypeChecker(TermTypeChecker termTypeChecker, FormulaTypeChecker formulaTypeChecker) {
        this.termTypeChecker = termTypeChecker;
        this.formulaTypeChecker = formulaTypeChecker;
    }

    public void analyse(FunctionDefinition function, List<FunctionPrototype> functionPrototypes)
            throws TypeMismatchException {

        try {
            function.accept(new FunctionTypeCheckingVisitor(functionPrototypes));
        } catch (WrappingRuntimeException wre) {
            Exception wrapped = wre.getWrappedException();
            if (wrapped instanceof TypeMismatchException) {
                throw (TypeMismatchException) wrapped;
            }
            throw wre;
        }
    }

    private class FunctionTypeCheckingVisitor implements FunctionDefinitionVisitor<Void> {

        private final List<FunctionPrototype> functionPrototypes;

        private FunctionTypeCheckingVisitor(List<FunctionPrototype> functionPrototypes) {
            this.functionPrototypes = functionPrototypes;
        }

        @Override
        public Void visit(FunctionDefinition function) {
            return function.accept(this);
        }

        @Override
        public Void visitMathematicalFunctionDefinition(MathematicalFunctionDefinition mathematicalFunction) {

            for (FunctionCase functionCase : mathematicalFunction.getCases()) {
                try {
                    Term expression = functionCase.getExpression();
                    if (expression.getType() != mathematicalFunction.getReturnType()) {
                        throw new TypeMismatchException("Return expression not of correct type: " + expression);
                    }

                    termTypeChecker.analyse(expression, functionPrototypes);
                    formulaTypeChecker.analyse(functionCase.getCondition(), functionPrototypes);
                } catch (TypeMismatchException e) {
                    throw new WrappingRuntimeException(e);
                }
            }

            return null;
        }
    }

}

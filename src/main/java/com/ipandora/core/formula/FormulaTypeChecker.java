package com.ipandora.core.formula;

import com.ipandora.api.predicate.formula.*;
import com.ipandora.api.predicate.function.FunctionPrototype;
import com.ipandora.api.predicate.term.Term;
import com.ipandora.api.predicate.term.Type;
import com.ipandora.api.predicate.term.TypeMismatchException;
import com.ipandora.core.term.TermTypeChecker;
import com.ipandora.core.util.WrappingRuntimeException;

import java.util.List;

public class FormulaTypeChecker {

    private final TermTypeChecker termTypeChecker;

    public FormulaTypeChecker(TermTypeChecker termTypeChecker) {
        this.termTypeChecker = termTypeChecker;
    }

    public void analyse(Formula formula, List<FunctionPrototype> functionPrototypes) throws TypeMismatchException {
        try {
            formula.accept(new FormulaTypeCheckingVisitor(functionPrototypes));
        } catch (WrappingRuntimeException wre) {
            Exception wrapped = wre.getWrappedException();
            if (wrapped instanceof TypeMismatchException) {
                throw (TypeMismatchException) wrapped;
            }
            throw wre;
        }
    }

    private class FormulaTypeCheckingVisitor implements FormulaVisitor<Void> {

        private final List<FunctionPrototype> functionPrototypes;

        private FormulaTypeCheckingVisitor(List<FunctionPrototype> functionPrototypes) {
            this.functionPrototypes = functionPrototypes;
        }

        @Override
        public Void visit(Formula formula) {
            formula.accept(this);
            return null;
        }

        @Override
        public Void visitAndFormula(AndFormula andFormula) {
            visit(andFormula.getLeft());
            visit(andFormula.getRight());
            return null;
        }

        @Override
        public Void visitOrFormula(OrFormula orFormula) {
            visit(orFormula.getLeft());
            visit(orFormula.getRight());
            return null;
        }

        @Override
        public Void visitForallFormula(ForallFormula forallFormula) {
            visit(forallFormula.getFormula());
            return null;
        }

        @Override
        public Void visitExistsFormula(ExistsFormula existsFormula) {
            visit(existsFormula.getFormula());
            return null;
        }

        @Override
        public Void visitTruthFormula(TruthFormula truthFormula) {
            return null;
        }

        @Override
        public Void visitFalsityFormula(FalsityFormula falsityFormula) {
            return null;
        }

        @Override
        public Void visitImpliesFormula(ImpliesFormula impliesFormula) {
            visit(impliesFormula.getLeft());
            visit(impliesFormula.getRight());
            return null;
        }

        @Override
        public Void visitIffFormula(IffFormula iffFormula) {
            visit(iffFormula.getLeft());
            visit(iffFormula.getRight());
            return null;
        }

        @Override
        public Void visitNotFormula(NotFormula notFormula) {
            visit(notFormula.getFormula());
            return null;
        }

        @Override
        public Void visitPropositionFormula(PropositionFormula propositionFormula) {
            return null;
        }

        @Override
        public Void visitPredicateFormula(PredicateFormula predicateFormula) {
            List<Term> params = predicateFormula.getParams();

            for (Term param : params) {
                try {
                    termTypeChecker.analyse(param, functionPrototypes);
                } catch (TypeMismatchException e) {
                    throw new WrappingRuntimeException(e);
                }
            }

            return null;
        }

        @Override
        public Void visitEqualToFormula(EqualToFormula equalToFormula) {
            visitMathematicalComparisonFormula(equalToFormula);
            return null;
        }

        @Override
        public Void visitGreaterThanFormula(GreaterThanFormula greaterThanFormula) {
            visitMathematicalComparisonFormula(greaterThanFormula);
            return null;
        }

        @Override
        public Void visitLessThanFormula(LessThanFormula lessThanFormula) {
            visitMathematicalComparisonFormula(lessThanFormula);
            return null;
        }

        @Override
        public Void visitGreaterThanEqualFormula(GreaterThanEqualFormula greaterThanEqualFormula) {
            visitMathematicalComparisonFormula(greaterThanEqualFormula);
            return null;
        }

        @Override
        public Void visitLessThanEqualFormula(LessThanEqualFormula lessThanEqualFormula) {
            visitMathematicalComparisonFormula(lessThanEqualFormula);
            return null;
        }

        private void visitMathematicalComparisonFormula(MathematicalComparisonFormula formula) {
            Term left = formula.getLeft();
            Term right = formula.getRight();

            if (left.getType() != Type.NAT) {
                throw new WrappingRuntimeException(new TypeMismatchException("Left term not of type Nat: " + left));
            }
            if (right.getType() != Type.NAT) {
                throw new WrappingRuntimeException(new TypeMismatchException("Right term not of type Nat: " + right));
            }

            try {
                termTypeChecker.analyse(left, functionPrototypes);
                termTypeChecker.analyse(right, functionPrototypes);
            } catch (TypeMismatchException e) {
                throw new WrappingRuntimeException(e);
            }
        }
    }

}

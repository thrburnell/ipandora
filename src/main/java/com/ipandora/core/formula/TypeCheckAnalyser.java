package com.ipandora.core.formula;

import com.ipandora.api.predicate.formula.*;
import com.ipandora.api.predicate.term.Term;
import com.ipandora.api.predicate.term.Type;
import com.ipandora.api.predicate.term.TypeMismatchException;
import com.ipandora.core.term.TermTypeChecker;
import com.ipandora.core.util.WrappingRuntimeException;

import java.util.List;

public class TypeCheckAnalyser implements FormulaSemanticAnalyser, FormulaVisitor<Void> {

    private final TermTypeChecker termTypeChecker;

    public TypeCheckAnalyser(TermTypeChecker termTypeChecker) {
        this.termTypeChecker = termTypeChecker;
    }

    @Override
    public void analyse(Formula formula) {
        formula.accept(this);
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
            termTypeChecker.visit(param);
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

        termTypeChecker.visit(left);
        termTypeChecker.visit(right);
    }

}

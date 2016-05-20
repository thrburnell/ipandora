package com.ipandora.core.formula;

import com.ipandora.api.predicate.formula.*;
import com.ipandora.api.predicate.term.Term;
import com.ipandora.api.predicate.term.Variable;
import com.ipandora.core.term.TermVisitor;

public class TermVisitingFormulaVisitor implements FormulaVisitor<Void> {

    private final TermVisitor<?> termVisitor;

    public TermVisitingFormulaVisitor(TermVisitor<?> termVisitor) {
        this.termVisitor = termVisitor;
    }

    @Override
    public Void visit(Formula formula) {
        return formula.accept(this);
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
        return visitQuantifiedFormula(forallFormula);
    }

    @Override
    public Void visitExistsFormula(ExistsFormula existsFormula) {
        return visitQuantifiedFormula(existsFormula);
    }

    private Void visitQuantifiedFormula(QuantifiedFormula quantifiedFormula) {
        for (Variable variable : quantifiedFormula.getVariables()) {
            termVisitor.visit(variable);
        }
        visit(quantifiedFormula.getFormula());
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
        for (Term param : predicateFormula.getParams()) {
            termVisitor.visit(param);
        }
        return null;
    }

    @Override
    public Void visitEqualToFormula(EqualToFormula equalToFormula) {
        return visitMathematicalComparisonFormula(equalToFormula);
    }

    @Override
    public Void visitGreaterThanFormula(GreaterThanFormula greaterThanFormula) {
        return visitMathematicalComparisonFormula(greaterThanFormula);
    }

    @Override
    public Void visitLessThanFormula(LessThanFormula lessThanFormula) {
        return visitMathematicalComparisonFormula(lessThanFormula);
    }

    @Override
    public Void visitGreaterThanEqualFormula(GreaterThanEqualFormula greaterThanEqualFormula) {
        return visitMathematicalComparisonFormula(greaterThanEqualFormula);
    }

    @Override
    public Void visitLessThanEqualFormula(LessThanEqualFormula lessThanEqualFormula) {
        return visitMathematicalComparisonFormula(lessThanEqualFormula);
    }

    private Void visitMathematicalComparisonFormula(MathematicalComparisonFormula formula) {
        termVisitor.visit(formula.getLeft());
        termVisitor.visit(formula.getRight());
        return null;
    }

}

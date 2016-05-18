package com.ipandora.core.formula;

import com.ipandora.api.predicate.formula.*;
import com.ipandora.api.predicate.term.*;
import com.ipandora.api.predicate.term.Number;
import com.ipandora.core.term.TermVisitor;

import java.util.HashSet;
import java.util.Set;

public class AtomicTermCollector {

    public Set<Atom> collectAtoms(Formula formula) {
        Set<Atom> atoms = new HashSet<>();
        CollectingFormulaVisitor formulaVisitor = new CollectingFormulaVisitor(atoms);
        formulaVisitor.visit(formula);
        return atoms;
    }

    private class CollectingFormulaVisitor implements FormulaVisitor<Void> {

        private final Set<Atom> atoms;
        private final CollectingTermVisitor termVisitor;

        private CollectingFormulaVisitor(Set<Atom> atoms) {
            this.atoms = atoms;
            this.termVisitor = new CollectingTermVisitor(atoms);
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
            atoms.add(forallFormula.getVariable());
            visit(forallFormula.getFormula());
            return null;
        }

        @Override
        public Void visitExistsFormula(ExistsFormula existsFormula) {
            atoms.add(existsFormula.getVariable());
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

    private class CollectingTermVisitor implements TermVisitor<Void> {

        private final Set<Atom> atoms;

        private CollectingTermVisitor(Set<Atom> atoms) {
            this.atoms = atoms;
        }

        @Override
        public Void visit(Term term) {
            return term.accept(this);
        }

        @Override
        public Void visitConstant(Constant constant) {
            atoms.add(constant);
            return null;
        }

        @Override
        public Void visitVariable(Variable variable) {
            atoms.add(variable);
            return null;
        }

        @Override
        public Void visitAddition(Addition addition) {
            return visitArithmeticExpression(addition);
        }

        @Override
        public Void visitSubtraction(Subtraction subtraction) {
            return visitArithmeticExpression(subtraction);
        }

        @Override
        public Void visitMultiplication(Multiplication multiplication) {
            return visitArithmeticExpression(multiplication);
        }

        @Override
        public Void visitDivision(Division division) {
            return visitArithmeticExpression(division);
        }

        private Void visitArithmeticExpression(ArithmeticExpression expression) {
            visit(expression.getLeft());
            visit(expression.getRight());
            return null;
        }

        @Override
        public Void visitNumber(Number number) {
            atoms.add(number);
            return null;
        }

        @Override
        public Void visitFunction(Function function) {
            atoms.add(function);
            for (Term arg : function.getArgs()) {
                visit(arg);
            }
            return null;
        }

        @Override
        public Void visitPower(Power power) {
            visit(power.getBase());
            return null;
        }

        @Override
        public Void visitSummation(Summation summation) {
            visit(summation.getVariable());
            visit(summation.getLowerBound());
            visit(summation.getUpperBound());
            visit(summation.getElement());
            return null;
        }

    }

}

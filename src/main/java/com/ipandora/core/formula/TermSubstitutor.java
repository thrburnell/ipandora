package com.ipandora.core.formula;

import com.ipandora.api.predicate.formula.*;
import com.ipandora.api.predicate.term.*;
import com.ipandora.api.predicate.term.Number;
import com.ipandora.core.term.TermVisitor;

import java.util.ArrayList;
import java.util.List;

public class TermSubstitutor {

    // TODO: can this be made generic, to return the same <T extends Formula> as is given?
    public Formula cloneAndSubstituteInScope(Formula formula, Term t1, Term t2) {
        SubstitutingFormulaVisitor substitutingFormulaVisitor = new SubstitutingFormulaVisitor(t1, t2);
        return substitutingFormulaVisitor.visit(formula);
    }

    private class SubstitutingFormulaVisitor implements FormulaVisitor<Formula> {

        private final Term t1;
        private final Term t2;
        private final SubstitutingTermVisitor substitutingTermVisitor;

        SubstitutingFormulaVisitor(Term t1, Term t2) {
            this.t1 = t1;
            this.t2 = t2;
            this.substitutingTermVisitor = new SubstitutingTermVisitor(t1, t2);
        }

        @Override
        public Formula visit(Formula formula) {
            return formula.accept(this);
        }

        @Override
        public Formula visitAndFormula(AndFormula andFormula) {
            Formula left = visit(andFormula.getLeft());
            Formula right = visit(andFormula.getRight());
            return new AndFormula(left, right);
        }

        @Override
        public Formula visitOrFormula(OrFormula orFormula) {
            Formula left = visit(orFormula.getLeft());
            Formula right = visit(orFormula.getRight());
            return new OrFormula(left, right);
        }

        @Override
        public Formula visitForallFormula(ForallFormula forallFormula) {
            String varName = forallFormula.getVariable().getName();
            substitutingTermVisitor.ignoreFromSubstitution(varName);
            Formula result = visit(forallFormula.getFormula());
            substitutingTermVisitor.removeFromIgnoreList(varName);
            return new ForallFormula(forallFormula.getVariable(), result);
        }

        @Override
        public Formula visitExistsFormula(ExistsFormula existsFormula) {
            String varName = existsFormula.getVariable().getName();
            substitutingTermVisitor.ignoreFromSubstitution(varName);
            Formula result = visit(existsFormula.getFormula());
            substitutingTermVisitor.removeFromIgnoreList(varName);
            return new ExistsFormula(existsFormula.getVariable(), result);
        }

        @Override
        public Formula visitTruthFormula(TruthFormula truthFormula) {
            return new TruthFormula();
        }

        @Override
        public Formula visitFalsityFormula(FalsityFormula falsityFormula) {
            return new FalsityFormula();
        }

        @Override
        public Formula visitImpliesFormula(ImpliesFormula impliesFormula) {
            Formula left = visit(impliesFormula.getLeft());
            Formula right = visit(impliesFormula.getRight());
            return new ImpliesFormula(left, right);
        }

        @Override
        public Formula visitIffFormula(IffFormula iffFormula) {
            Formula left = visit(iffFormula.getLeft());
            Formula right = visit(iffFormula.getRight());
            return new IffFormula(left, right);
        }

        @Override
        public Formula visitNotFormula(NotFormula notFormula) {
            Formula formula = visit(notFormula.getFormula());
            return new NotFormula(formula);
        }

        @Override
        public Formula visitPropositionFormula(PropositionFormula propositionFormula) {
            return new PropositionFormula(propositionFormula.getName());
        }

        @Override
        public Formula visitPredicateFormula(PredicateFormula predicateFormula) {
            List<Term> newParams = new ArrayList<>();

            for (Term param : predicateFormula.getParams()) {
                newParams.add(substitutingTermVisitor.visit(param));
            }

            return new PredicateFormula(predicateFormula.getName(), newParams);
        }

        @Override
        public Formula visitEqualToFormula(EqualToFormula equalToFormula) {
            Term left = substitutingTermVisitor.visit(equalToFormula.getLeft());
            Term right = substitutingTermVisitor.visit(equalToFormula.getRight());
            return new EqualToFormula(left, right);
        }

        @Override
        public Formula visitGreaterThanFormula(GreaterThanFormula greaterThanFormula) {
            Term left = substitutingTermVisitor.visit(greaterThanFormula.getLeft());
            Term right = substitutingTermVisitor.visit(greaterThanFormula.getRight());
            return new GreaterThanFormula(left, right);
        }

        @Override
        public Formula visitLessThanFormula(LessThanFormula lessThanFormula) {
            Term left = substitutingTermVisitor.visit(lessThanFormula.getLeft());
            Term right = substitutingTermVisitor.visit(lessThanFormula.getRight());
            return new LessThanFormula(left, right);
        }

        @Override
        public Formula visitGreaterThanEqualFormula(GreaterThanEqualFormula greaterThanEqualFormula) {
            Term left = substitutingTermVisitor.visit(greaterThanEqualFormula.getLeft());
            Term right = substitutingTermVisitor.visit(greaterThanEqualFormula.getRight());
            return new GreaterThanEqualFormula(left, right);
        }

        @Override
        public Formula visitLessThanEqualFormula(LessThanEqualFormula lessThanEqualFormula) {
            Term left = substitutingTermVisitor.visit(lessThanEqualFormula.getLeft());
            Term right = substitutingTermVisitor.visit(lessThanEqualFormula.getRight());
            return new LessThanEqualFormula(left, right);
        }

    }

    private class SubstitutingTermVisitor implements TermVisitor<Term> {

        // Needs to be a List to support vars introduced multiple times e.g. forall ?x (forall ?x (?x = 2))
        private final List<String> varsIgnoring = new ArrayList<>();
        private final Term t1;
        private final Term t2;

        SubstitutingTermVisitor(Term t1, Term t2) {
            this.t1 = t1;
            this.t2 = t2;
        }

        @Override
        public Term visit(Term term) {
            return term.accept(this);
        }

        @Override
        public Term visitConstant(Constant constant) {
            return constant.equals(t1) ? t2 : constant;
        }

        @Override
        public Term visitVariable(Variable variable) {
            return variable.equals(t1) && !varsIgnoring.contains(variable.getName()) ? t2 : variable;
        }

        @Override
        public Term visitAddition(Addition addition) {

            if (addition.equals(t1)) {
                return t2;
            }

            Term left = visit(addition.getLeft());
            Term right = visit(addition.getRight());

            return new Addition(left, right);
        }

        @Override
        public Term visitSubtraction(Subtraction subtraction) {

            if (subtraction.equals(t1)) {
                return t2;
            }

            Term left = visit(subtraction.getLeft());
            Term right = visit(subtraction.getRight());

            return new Subtraction(left, right);
        }

        @Override
        public Term visitMultiplication(Multiplication multiplication) {

            if (multiplication.equals(t1)) {
                return t2;
            }

            Term left = visit(multiplication.getLeft());
            Term right = visit(multiplication.getRight());

            return new Multiplication(left, right);
        }

        @Override
        public Term visitDivision(Division division) {

            if (division.equals(t1)) {
                return t2;
            }

            Term left = visit(division.getLeft());
            Term right = visit(division.getRight());

            return new Division(left, right);
        }

        @Override
        public Term visitNumber(Number number) {
            return number.equals(t1) ? t2 : number;
        }

        @Override
        public Term visitFunction(Function function) {

            if (function.equals(t1)) {
                return t2;
            }

            List<Term> newArgs = new ArrayList<>();
            for (Term arg : function.getArgs()) {
                newArgs.add(visit(arg));
            }

            return new Function(function.getName(), newArgs, function.getType());
        }

        @Override
        public Term visitPower(Power power) {

            if (power.equals(t1)) {
                return t2;
            }

            Term base = visit(power.getBase());

            return new Power(base, power.getExponent());
        }

        @Override
        public Term visitSummation(Summation summation) {

            if (summation.equals(t1)) {
                return t2;
            }

            Variable variable = summation.getVariable();
            ignoreFromSubstitution(variable.getName());

            Term lowerBound = visit(summation.getLowerBound());
            Term upperBound = visit(summation.getUpperBound());
            Term element = visit(summation.getElement());

            removeFromIgnoreList(variable.getName());

            return new Summation(variable, lowerBound, upperBound, element);
        }

        void ignoreFromSubstitution(String name) {
            varsIgnoring.add(name);
        }

        void removeFromIgnoreList(String name) {
            varsIgnoring.remove(name);
        }
    }

}

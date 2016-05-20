package com.ipandora.testutils;

import com.ipandora.api.predicate.formula.*;
import com.ipandora.api.predicate.term.Term;
import com.ipandora.api.predicate.term.Variable;

import java.util.Arrays;

public class FormulaCreators {

    // Connectives
    public static AndFormula and(Formula f1, Formula f2, Formula... fs) {
        AndFormula andFormula = new AndFormula(f1, f2);

        for (Formula f : fs) {
            andFormula = new AndFormula(andFormula, f);
        }

        return andFormula;
    }

    public static OrFormula or(Formula f1, Formula f2, Formula... fs) {
        OrFormula orFormula = new OrFormula(f1, f2);

        for (Formula f : fs) {
            orFormula = new OrFormula(orFormula, f);
        }

        return orFormula;
    }

    public static ImpliesFormula imp(Formula f1, Formula f2, Formula... fs) {
        ImpliesFormula impliesFormula = new ImpliesFormula(f1, f2);

        for (Formula f : fs) {
            impliesFormula = new ImpliesFormula(impliesFormula, f);
        }

        return impliesFormula;
    }

    public static IffFormula iff(Formula f1, Formula f2, Formula... fs) {
        IffFormula iffFormula = new IffFormula(f1, f2);

        for (Formula f : fs) {
            iffFormula = new IffFormula(iffFormula, f);
        }

        return iffFormula;
    }

    // Boolean expressions
    public static EqualToFormula eq(Term t1, Term t2) {
        return new EqualToFormula(t1, t2);
    }

    public static GreaterThanFormula gt(Term t1, Term t2) {
        return new GreaterThanFormula(t1, t2);
    }

    public static LessThanFormula lt(Term t1, Term t2) {
        return new LessThanFormula(t1, t2);
    }

    public static GreaterThanEqualFormula gte(Term t1, Term t2) {
        return new GreaterThanEqualFormula(t1, t2);
    }

    public static LessThanEqualFormula lte(Term t1, Term t2) {
        return new LessThanEqualFormula(t1, t2);
    }

    // Quantified
    public static ExistsFormula exists(Formula formula, Variable... variables) {
        return new ExistsFormula(formula, variables);
    }

    public static ForallFormula forall(Formula formula, Variable... variables) {
        return new ForallFormula(formula, variables);
    }

    // Atomic
    public static TruthFormula truth() {
        return new TruthFormula();
    }

    public static FalsityFormula falsity() {
        return new FalsityFormula();
    }

    // Other
    public static PredicateFormula pred(String name, Term... terms) {
        return new PredicateFormula(name, Arrays.asList(terms));
    }

    public static PropositionFormula prop(String name) {
        return new PropositionFormula(name);
    }

    public static NotFormula not(Formula formula) {
        return new NotFormula(formula);
    }

}

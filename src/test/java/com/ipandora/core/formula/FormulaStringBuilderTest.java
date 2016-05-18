package com.ipandora.core.formula;

import com.ipandora.api.predicate.formula.*;
import com.ipandora.api.predicate.term.Number;
import com.ipandora.api.predicate.term.Term;
import com.ipandora.api.predicate.term.Variable;
import com.ipandora.core.term.TermStringBuilder;
import org.junit.Test;

import java.util.Arrays;
import java.util.List;

import static org.assertj.core.api.Assertions.assertThat;

public class FormulaStringBuilderTest {

    private static final PropositionFormula P = new PropositionFormula("P");
    private static final PropositionFormula Q = new PropositionFormula("Q");
    private static final PropositionFormula R = new PropositionFormula("R");

    private static final Variable X = new Variable("?x");
    private static final Variable Y = new Variable("?y");

    private static List<Term> list(Term... term) {
        return Arrays.asList(term);
    }

    @Test
    public void buildForallEqualToNotSoNoBrackets() {
        // \FORALL ?x !P(?x)
        FormulaStringBuilder builder = new FormulaStringBuilder(new TermStringBuilder());
        ForallFormula formula = new ForallFormula(X, new NotFormula(new PredicateFormula("P", list(X))));
        String result = builder.build(formula);

        assertThat(result).isEqualTo("\\FORALL ?x !P(?x)");
    }

    @Test
    public void buildForallStrongerThanAndSoNoBrackets() {
        // \FORALL ?x \FORALL ?y P(?y) & P(?x)
        FormulaStringBuilder builder = new FormulaStringBuilder(new TermStringBuilder());
        ForallFormula forallY = new ForallFormula(Y, new PredicateFormula("P", list(Y)));
        ForallFormula formula = new ForallFormula(X, new AndFormula(forallY, new PredicateFormula("P", list(X))));
        String result = builder.build(formula);

        assertThat(result).isEqualTo("\\FORALL ?x (\\FORALL ?y P(?y) & P(?x))");
    }

    @Test
    public void buildForallStrongerThanAndSoBrackets() {
        // \FORALL ?x \FORALL ?y (P(?y) & P(?x))
        FormulaStringBuilder builder = new FormulaStringBuilder(new TermStringBuilder());
        PredicateFormula pY = new PredicateFormula("P", list(Y));
        PredicateFormula pX = new PredicateFormula("P", list(X));
        ForallFormula formula = new ForallFormula(X, new ForallFormula(Y, new AndFormula(pY, pX)));
        String result = builder.build(formula);

        assertThat(result).isEqualTo("\\FORALL ?x \\FORALL ?y (P(?y) & P(?x))");
    }

    @Test
    public void buildExistsEqualToNotSoNoBrackets() {
        // \EXISTS ?x !P(?x)
        FormulaStringBuilder builder = new FormulaStringBuilder(new TermStringBuilder());
        ExistsFormula formula = new ExistsFormula(X, new NotFormula(new PredicateFormula("P", list(X))));
        String result = builder.build(formula);

        assertThat(result).isEqualTo("\\EXISTS ?x !P(?x)");
    }

    @Test
    public void buildExistsStrongerThanAndSoNoBrackets() {
        // \EXISTS ?x \EXISTS ?y P(?y) & P(?x)
        FormulaStringBuilder builder = new FormulaStringBuilder(new TermStringBuilder());
        ExistsFormula existsY = new ExistsFormula(Y, new PredicateFormula("P", list(Y)));
        ExistsFormula formula = new ExistsFormula(X, new AndFormula(existsY, new PredicateFormula("P", list(X))));
        String result = builder.build(formula);

        assertThat(result).isEqualTo("\\EXISTS ?x (\\EXISTS ?y P(?y) & P(?x))");
    }

    @Test
    public void buildExistsStrongerThanAndSoBrackets() {
        // \EXISTS ?x \EXISTS ?y (P(?y) & P(?x))
        FormulaStringBuilder builder = new FormulaStringBuilder(new TermStringBuilder());
        PredicateFormula pY = new PredicateFormula("P", list(Y));
        PredicateFormula pX = new PredicateFormula("P", list(X));
        ExistsFormula formula = new ExistsFormula(X, new ExistsFormula(Y, new AndFormula(pY, pX)));
        String result = builder.build(formula);

        assertThat(result).isEqualTo("\\EXISTS ?x \\EXISTS ?y (P(?y) & P(?x))");
    }

    @Test
    public void buildNotStrongerThanAndSoNoBrackets() {
        // !P & Q
        FormulaStringBuilder builder = new FormulaStringBuilder(new TermStringBuilder());
        AndFormula formula = new AndFormula(new NotFormula(P), Q);
        String result = builder.build(formula);

        assertThat(result).isEqualTo("!P & Q");
    }

    @Test
    public void buildNotStrongerThanAndSoBrackets() {
        // !(P & Q)
        FormulaStringBuilder builder = new FormulaStringBuilder(new TermStringBuilder());
        NotFormula formula = new NotFormula(new AndFormula(P, Q));
        String result = builder.build(formula);

        assertThat(result).isEqualTo("!(P & Q)");
    }

    @Test
    public void buildAndStrongerThanOrSoNoBrackets() {
        // P & Q | R
        FormulaStringBuilder builder = new FormulaStringBuilder(new TermStringBuilder());
        OrFormula formula = new OrFormula(new AndFormula(P, Q), R);
        String result = builder.build(formula);

        assertThat(result).isEqualTo("P & Q | R");
    }

    @Test
    public void buildAndStrongerThanOrSoBrackets() {
        // P & (Q | R)
        FormulaStringBuilder builder = new FormulaStringBuilder(new TermStringBuilder());
        AndFormula formula = new AndFormula(P, new OrFormula(Q, R));
        String result = builder.build(formula);

        assertThat(result).isEqualTo("P & (Q | R)");
    }

    @Test
    public void buildOrStrongerThanImpliesSoNoBrackets() {
        // P | Q -> R
        FormulaStringBuilder builder = new FormulaStringBuilder(new TermStringBuilder());
        ImpliesFormula formula = new ImpliesFormula(new OrFormula(P, Q), R);
        String result = builder.build(formula);

        assertThat(result).isEqualTo("P | Q -> R");
    }

    @Test
    public void buildOrStrongerThanImpliesSoBrackets() {
        // P | (Q -> R)
        FormulaStringBuilder builder = new FormulaStringBuilder(new TermStringBuilder());
        OrFormula formula = new OrFormula(P, new ImpliesFormula(Q, R));
        String result = builder.build(formula);

        assertThat(result).isEqualTo("P | (Q -> R)");
    }

    @Test
    public void buildImpliesStrongerThanIffSoNoBrackets() {
        // P -> Q <-> R
        FormulaStringBuilder builder = new FormulaStringBuilder(new TermStringBuilder());
        IffFormula formula = new IffFormula(new ImpliesFormula(P, Q), R);
        String result = builder.build(formula);

        assertThat(result).isEqualTo("P -> Q <-> R");
    }

    @Test
    public void buildImpliesStrongerThanIffSoBrackets() {
        // P -> (Q <-> R)
        FormulaStringBuilder builder = new FormulaStringBuilder(new TermStringBuilder());
        ImpliesFormula formula = new ImpliesFormula(P, new IffFormula(Q, R));
        String result = builder.build(formula);

        assertThat(result).isEqualTo("P -> (Q <-> R)");
    }

    @Test
    public void buildNestedQuantifiersShouldHaveNoBrackets() {
        // \FORALL ?x \EXISTS ?y P(?x, ?y)
        FormulaStringBuilder builder = new FormulaStringBuilder(new TermStringBuilder());
        ForallFormula formula = new ForallFormula(X, new ExistsFormula(Y, new PredicateFormula("P", list(X, Y))));
        String result = builder.build(formula);

        assertThat(result).isEqualTo("\\FORALL ?x \\EXISTS ?y P(?x, ?y)");
    }

    @Test
    public void buildNestedNotShouldHaveNoBrackets() {
        // !!!P
        FormulaStringBuilder builder = new FormulaStringBuilder(new TermStringBuilder());
        NotFormula formula = new NotFormula(new NotFormula(new NotFormula(P)));
        String result = builder.build(formula);

        assertThat(result).isEqualTo("!!!P");
    }

    @Test
    public void buildNestedAndShouldHaveNoBrackets() {
        // P & Q & R
        FormulaStringBuilder builder = new FormulaStringBuilder(new TermStringBuilder());
        AndFormula formula = new AndFormula(P, new AndFormula(Q, R));
        String result = builder.build(formula);

        assertThat(result).isEqualTo("P & Q & R");
    }

    @Test
    public void buildNestedOrShouldHaveNoBrackets() {
        // P | Q | R
        FormulaStringBuilder builder = new FormulaStringBuilder(new TermStringBuilder());
        OrFormula formula = new OrFormula(P, new OrFormula(Q, R));
        String result = builder.build(formula);

        assertThat(result).isEqualTo("P | Q | R");
    }

    @Test
    public void buildNestedImpliesShouldHaveBrackets() {
        // P -> (Q -> R)
        FormulaStringBuilder builder = new FormulaStringBuilder(new TermStringBuilder());
        ImpliesFormula formula = new ImpliesFormula(P, new ImpliesFormula(Q, R));
        String result = builder.build(formula);

        assertThat(result).isEqualTo("P -> (Q -> R)");

        // (P -> Q) -> R
        formula = new ImpliesFormula(new ImpliesFormula(P, Q), R);
        result = builder.build(formula);

        assertThat(result).isEqualTo("(P -> Q) -> R");
    }

    @Test
    public void buildNestedIffShouldHaveBrackets() {
        // P <-> (Q <-> R)
        FormulaStringBuilder builder = new FormulaStringBuilder(new TermStringBuilder());
        IffFormula formula = new IffFormula(P, new IffFormula(Q, R));
        String result = builder.build(formula);

        assertThat(result).isEqualTo("P <-> (Q <-> R)");

        // (P <-> Q) <-> R
        formula = new IffFormula(new IffFormula(P, Q), R);
        result = builder.build(formula);

        assertThat(result).isEqualTo("(P <-> Q) <-> R");
    }

    // !(?x = 2)
    // (?x = 2) & (?y = 3)

    @Test
    public void buildEqualToShouldNotHaveBracketsIfInOutermostContext() {
        // ?x = 2
        FormulaStringBuilder builder = new FormulaStringBuilder(new TermStringBuilder());
        EqualToFormula formula = new EqualToFormula(X, new Number(2));
        String result = builder.build(formula);

        assertThat(result).isEqualTo("?x = 2");
    }

    @Test
    public void buildGreaterThanShouldNotHaveBracketsIfInOutermostContext() {
        // ?x > 2
        FormulaStringBuilder builder = new FormulaStringBuilder(new TermStringBuilder());
        GreaterThanFormula formula = new GreaterThanFormula(X, new Number(2));
        String result = builder.build(formula);

        assertThat(result).isEqualTo("?x > 2");
    }

    @Test
    public void buildGreaterThanEqualShouldNotHaveBracketsIfInOutermostContext() {
        // ?x >= 2
        FormulaStringBuilder builder = new FormulaStringBuilder(new TermStringBuilder());
        GreaterThanEqualFormula formula = new GreaterThanEqualFormula(X, new Number(2));
        String result = builder.build(formula);

        assertThat(result).isEqualTo("?x >= 2");
    }

    @Test
    public void buildLessThanShouldNotHaveBracketsIfInOutermostContext() {
        // ?x < 2
        FormulaStringBuilder builder = new FormulaStringBuilder(new TermStringBuilder());
        LessThanFormula formula = new LessThanFormula(X, new Number(2));
        String result = builder.build(formula);

        assertThat(result).isEqualTo("?x < 2");
    }

    @Test
    public void buildLessThanEqualShouldNotHaveBracketsIfInOutermostContext() {
        // ?x <= 2
        FormulaStringBuilder builder = new FormulaStringBuilder(new TermStringBuilder());
        LessThanEqualFormula formula = new LessThanEqualFormula(X, new Number(2));
        String result = builder.build(formula);

        assertThat(result).isEqualTo("?x <= 2");
    }

    @Test
    public void buildEqualToShouldHaveBracketsIfNotInOutermostContext() {
        // !(?x = 2)
        FormulaStringBuilder builder = new FormulaStringBuilder(new TermStringBuilder());
        NotFormula formula = new NotFormula(new EqualToFormula(X, new Number(2)));
        String result = builder.build(formula);

        assertThat(result).isEqualTo("!(?x = 2)");
    }

    @Test
    public void buildGreaterThanShouldHaveBracketsIfNotInOutermostContext() {
        // !(?x > 2)
        FormulaStringBuilder builder = new FormulaStringBuilder(new TermStringBuilder());
        NotFormula formula = new NotFormula(new GreaterThanFormula(X, new Number(2)));
        String result = builder.build(formula);

        assertThat(result).isEqualTo("!(?x > 2)");
    }

    @Test
    public void buildGreaterThanEqualShouldHaveBracketsIfNotInOutermostContext() {
        // !(?x >= 2)
        FormulaStringBuilder builder = new FormulaStringBuilder(new TermStringBuilder());
        NotFormula formula = new NotFormula(new GreaterThanEqualFormula(X, new Number(2)));
        String result = builder.build(formula);

        assertThat(result).isEqualTo("!(?x >= 2)");
    }

    @Test
    public void buildLessThanShouldHaveBracketsIfNotInOutermostContext() {
        // !(?x < 2)
        FormulaStringBuilder builder = new FormulaStringBuilder(new TermStringBuilder());
        NotFormula formula = new NotFormula(new LessThanFormula(X, new Number(2)));
        String result = builder.build(formula);

        assertThat(result).isEqualTo("!(?x < 2)");
    }

    @Test
    public void buildLessThanEqualShouldHaveBracketsIfNotInOutermostContext() {
        // !(?x <= 2)
        FormulaStringBuilder builder = new FormulaStringBuilder(new TermStringBuilder());
        NotFormula formula = new NotFormula(new LessThanEqualFormula(X, new Number(2)));
        String result = builder.build(formula);

        assertThat(result).isEqualTo("!(?x <= 2)");
    }

    @Test
    public void buildBooleanTermsShouldBeParenthesised() {
        // Admittedly this test also tests for nested &...
        // (?x = 2) & (?x > 1) & (?x >= 0) & (?x < 3) & (?x <= 2)
        FormulaStringBuilder builder = new FormulaStringBuilder(new TermStringBuilder());
        EqualToFormula eq = new EqualToFormula(X, new Number(2));
        GreaterThanFormula gt = new GreaterThanFormula(X, new Number(1));
        GreaterThanEqualFormula gte = new GreaterThanEqualFormula(X, new Number(0));
        LessThanFormula lt = new LessThanFormula(X, new Number(3));
        LessThanEqualFormula lte = new LessThanEqualFormula(X, new Number(2));
        AndFormula formula = new AndFormula(eq, new AndFormula(gt, new AndFormula(gte, new AndFormula(lt, lte))));
        String result = builder.build(formula);

        assertThat(result).isEqualTo("(?x = 2) & (?x > 1) & (?x >= 0) & (?x < 3) & (?x <= 2)");
    }


}

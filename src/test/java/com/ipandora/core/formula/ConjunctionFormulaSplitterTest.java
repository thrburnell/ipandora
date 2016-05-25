package com.ipandora.core.formula;

import com.ipandora.api.predicate.formula.*;
import org.junit.Before;
import org.junit.Test;

import java.util.List;

import static com.ipandora.testutils.FormulaCreators.*;
import static com.ipandora.testutils.TermCreators.*;
import static org.assertj.core.api.Assertions.assertThat;

public class ConjunctionFormulaSplitterTest {

    private ConjunctionFormulaSplitter splitter;

    @Before
    public void before() {
        splitter = new ConjunctionFormulaSplitter();
    }

    @Test
    public void splitShouldNotSplitIfLeftNorRightAreAndFormula() {
        EqualToFormula left = eq(var("x"), var("y"));
        NotFormula right = not(gte(var("z"), num(14)));
        List<Formula> split = splitter.split(and(left, right));

        assertThat(split).containsExactly(left, right);
    }

    @Test
    public void splitShouldReturnSplitOfLeftAndRightIfRightIsntAndFormula() {
        EqualToFormula l1 = eq(var("x"), var("y"));
        EqualToFormula l2 = eq(con("c"), num(2));
        AndFormula left = and(l1, l2);
        NotFormula right = not(gte(var("z"), num(14)));
        List<Formula> split = splitter.split(and(left, right));

        assertThat(split).containsExactly(l1, l2, right);
    }

    @Test
    public void splitShouldReturnSplitOfRightAndLeftIfLeftIsntAndFormula() {
        NotFormula left = not(gte(var("z"), num(14)));
        EqualToFormula r1 = eq(var("x"), var("y"));
        EqualToFormula r2 = eq(con("c"), num(2));
        AndFormula right = and(r1, r2);
        List<Formula> split = splitter.split(and(left, right));

        assertThat(split).containsExactly(left, r1, r2);
    }

    @Test
    public void splitShouldReturnSplitOfBothIfBothAreAndFormula() {
        NotFormula l1 = not(gte(var("z"), num(14)));
        NotFormula l2 = not(lte(con("d"), num(42)));
        EqualToFormula r1 = eq(var("x"), var("y"));
        EqualToFormula r2 = eq(con("c"), num(2));
        AndFormula left = and(l1, l2);
        AndFormula right = and(r1, r2);
        List<Formula> split = splitter.split(and(left, right));

        assertThat(split).containsExactly(l1, l2, r1, r2);
    }

    @Test
    public void splitShouldRecursivelySplitLeftAndRight() {
        PropositionFormula p = prop("P");
        PropositionFormula q = prop("Q");
        PropositionFormula r = prop("R");
        PropositionFormula s = prop("S");
        PropositionFormula t = prop("T");
        PropositionFormula u = prop("U");
        PropositionFormula v = prop("V");
        AndFormula left = and(p, q, r, s);
        AndFormula right = and(t, u, v);
        List<Formula> split = splitter.split(and(left, right));

        assertThat(split).containsExactly(p, q, r, s, t, u, v);
    }

}
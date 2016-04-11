package com.ipandora.core.formula;

import com.ipandora.api.predicate.formula.AndFormula;
import com.ipandora.api.predicate.formula.Formula;
import com.ipandora.api.predicate.formula.PredicateFormula;
import com.ipandora.api.predicate.term.Variable;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;

import static org.assertj.core.api.Assertions.assertThat;

public class FormulaConjunctionReducerTest {

    @Test
    public void reduceReturnsNullIfNoFormulasGiven() {
        FormulaConjunctionReducer formulaConjunctionReducer = new FormulaConjunctionReducer();
        Formula join = formulaConjunctionReducer.reduce(Collections.<Formula>emptyList());
        assertThat(join).isNull();
    }

    @Test
    public void reduceReturnsSingleFormulaIfSingletonListGiven() {
        FormulaConjunctionReducer formulaConjunctionReducer = new FormulaConjunctionReducer();
        Formula givenFormula = new PredicateFormula("Foo", Collections.singletonList(new Variable("x")));
        Formula join = formulaConjunctionReducer.reduce(Collections.singletonList(givenFormula));
        assertThat(join).isEqualTo(givenFormula);
    }

    @Test
    public void reduceReturnsAndOfTwoGivenFormulas() {
        FormulaConjunctionReducer formulaConjunctionReducer = new FormulaConjunctionReducer();
        PredicateFormula left = new PredicateFormula("Foo", Collections.singletonList(new Variable("x")));
        PredicateFormula right = new PredicateFormula("Bar", Collections.singletonList(new Variable("y")));
        Formula join = formulaConjunctionReducer.reduce(Arrays.<Formula>asList(left, right));
        assertThat(join).isEqualTo(new AndFormula(left, right));
    }

    @Test
    public void reduceReturnsAndOfThreeGivenFormulasUsingLeftAssociativity() {
        FormulaConjunctionReducer formulaConjunctionReducer = new FormulaConjunctionReducer();
        PredicateFormula foo = new PredicateFormula("Foo", Collections.singletonList(new Variable("x")));
        PredicateFormula bar = new PredicateFormula("Bar", Collections.singletonList(new Variable("y")));
        PredicateFormula baz = new PredicateFormula("Baz", Collections.singletonList(new Variable("z")));
        Formula join = formulaConjunctionReducer.reduce(Arrays.<Formula>asList(foo, bar, baz));
        assertThat(join).isEqualTo(new AndFormula(new AndFormula(foo, bar), baz));
    }

}

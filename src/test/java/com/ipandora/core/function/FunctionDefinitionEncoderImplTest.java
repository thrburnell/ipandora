package com.ipandora.core.function;

import com.ipandora.api.predicate.formula.AndFormula;
import com.ipandora.api.predicate.formula.ForallFormula;
import com.ipandora.api.predicate.formula.Formula;
import com.ipandora.api.predicate.formula.ImpliesFormula;
import com.ipandora.api.predicate.function.FunctionCase;
import com.ipandora.api.predicate.function.MathematicalFunctionDefinition;
import com.ipandora.api.predicate.term.Type;
import com.ipandora.api.predicate.term.Variable;
import com.ipandora.core.formula.ConjunctionFormulaSplitter;
import com.ipandora.core.formula.FormulaConjunctionReducer;
import org.junit.Before;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static com.ipandora.testutils.FormulaCreators.*;
import static com.ipandora.testutils.FunctionCreators.funCase;
import static com.ipandora.testutils.FunctionCreators.mathFun;
import static com.ipandora.testutils.TermCreators.*;
import static org.assertj.core.api.Assertions.assertThat;

public class FunctionDefinitionEncoderImplTest {

    private FunctionDefinitionEncoderImpl encoder;
    private ConjunctionFormulaSplitter andSplitter;

    @Before
    public void before() {
        encoder = new FunctionDefinitionEncoderImpl(new FormulaConjunctionReducer());
        andSplitter = new ConjunctionFormulaSplitter();
    }

    @Test
    public void encodeShouldQuantifyOverAllFunctionArguments() {
        /*
        f(x, y, z) = x + y + z
         */

        Variable x = natVar("x");
        Variable y = natVar("y");
        Variable z = natVar("z");

        FunctionCase fCase = funCase(add(x, y, z), truth());
        MathematicalFunctionDefinition f = mathFun("f", Arrays.asList(x, y, z), Collections.singletonList(fCase),
                Type.NAT);

        ForallFormula encoded = encoder.encode(f);
        List<Variable> variables = encoded.getVariables();
        assertThat(variables).containsExactlyInAnyOrder(x, y, z);
    }

    @Test
    public void encodeShouldGuardNatArguments() {
        /*
        f(x, y, z) =
            x + y + z   if x + y = 2
            z           otherwise
         */

        Variable x = natVar("x");
        Variable y = natVar("y");
        Variable z = natVar("z");

        FunctionCase c1 = funCase(add(x, y, z), eq(add(x, y), num(2)));
        FunctionCase c2 = funCase(z, not(eq(add(x, y), num(2))));
        MathematicalFunctionDefinition f = mathFun("f", Arrays.asList(x, y, z), Arrays.asList(c1, c2),
                Type.NAT);

        ForallFormula encoded = encoder.encode(f);
        Formula formula = encoded.getFormula();
        assertThat(formula).isInstanceOf(AndFormula.class);

        List<Formula> formulas = andSplitter.split((AndFormula) formula);
        assertThat(formulas).startsWith(gte(x, num(0)), gte(y, num(0)), gte(z, num(0)));
    }

    @Test
    public void encodeShouldCoverSingleFunctionCase() {
        /*
        f(x, y, z) = x + y + z
         */

        Variable x = natVar("x");
        Variable y = natVar("y");
        Variable z = natVar("z");

        FunctionCase fCase = funCase(add(x, y, z), truth());
        MathematicalFunctionDefinition f = mathFun("f", Arrays.asList(x, y, z), Collections.singletonList(fCase),
                Type.NAT);

        ImpliesFormula expected = imp(truth(), eq(natFun("f", x, y, z), add(x, y, z)));
        ForallFormula encoded = encoder.encode(f);
        Formula formula = encoded.getFormula();
        assertThat(formula).isInstanceOf(AndFormula.class);

        List<Formula> formulas = andSplitter.split((AndFormula) formula);
        assertThat(formulas).endsWith(expected);
    }

    @Test
    public void encodeShouldCoverTwoFunctionCases() {
        /*
        f(x) =
            0           if x = 0
            x + f(x-1)  otherwise
         */

        Variable x = natVar("x");
        FunctionCase c1 = funCase(num(0), eq(x, num(0)));
        FunctionCase c2 = funCase(add(x, natFun("f", sub(x, num(1)))), not(eq(x, num(0))));
        MathematicalFunctionDefinition f = mathFun("f", Collections.singletonList(x), Arrays.asList(c1, c2),
                Type.NAT);

        AndFormula expected = and(
                gte(x, num(0)),
                imp(eq(x, num(0)), eq(natFun("f", x), num(0))),
                imp(not(eq(x, num(0))), eq(natFun("f", x), add(x, natFun("f", sub(x, num(1)))))));

        ForallFormula encoded = encoder.encode(f);
        Formula formula = encoded.getFormula();
        assertThat(formula).isEqualTo(expected);
    }

    @Test
    public void encodeShouldCoverMultipleFunctionCases() {
        /*
        f(x) =
            0           if x = 0
            1           if x = 1
            x + f(x-1)  otherwise
         */

        Variable x = natVar("x");
        FunctionCase c1 = funCase(num(0), eq(x, num(0)));
        FunctionCase c2 = funCase(num(1), eq(x, num(1)));
        FunctionCase c3 = funCase(add(x, natFun("f", sub(x, num(1)))), and(not(eq(x, num(0))), not(eq(x, num(1)))));
        MathematicalFunctionDefinition f = mathFun("f", Collections.singletonList(x), Arrays.asList(c1, c2, c3),
                Type.NAT);

        ForallFormula encoded = encoder.encode(f);
        Formula formula = encoded.getFormula();
        assertThat(formula).isInstanceOf(AndFormula.class);

        List<Formula> formulas = andSplitter.split((AndFormula) formula);
        ImpliesFormula encodedCase1 = imp(eq(x, num(0)), eq(natFun("f", x), num(0)));
        ImpliesFormula encodedCase2 = imp(eq(x, num(1)), eq(natFun("f", x), num(1)));
        ImpliesFormula encodedCase3 = imp(and(not(eq(x, num(0))), not(eq(x, num(1)))),
                eq(natFun("f", x), add(x, natFun("f", sub(x, num(1))))));

        assertThat(formulas).endsWith(encodedCase1, encodedCase2, encodedCase3);
    }

}













package com.ipandora.core.z3;

import com.ipandora.api.predicate.formula.Formula;
import com.ipandora.api.predicate.term.Multiplication;
import com.ipandora.testutils.ContainedInCondition;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.mockito.ArgumentCaptor;
import org.mockito.Mock;
import org.mockito.runners.MockitoJUnitRunner;

import static com.ipandora.testutils.FormulaCreators.*;
import static com.ipandora.testutils.TermCreators.*;
import static org.assertj.core.api.Assertions.assertThat;
import static org.mockito.Matchers.any;
import static org.mockito.Matchers.anyString;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

@RunWith(MockitoJUnitRunner.class)
public class Z3ArithmeticEqualityCheckerTest {

    @Mock
    private SMTCodeGenerator mockCodeGenerator;

    @Mock
    private Z3Client mockZ3Client;

    private Z3ArithmeticEqualityChecker checker;

    @Before
    public void before() {
        checker = new Z3ArithmeticEqualityChecker(mockCodeGenerator, mockZ3Client);
    }

    @Test
    public void checkCallsZ3ClientWithGeneratedCode() throws Exception {
        String programCode = "generated-code";
        when(mockCodeGenerator.generateCheckSatCode(any(Formula.class)))
                .thenReturn(programCode);

        checker.check(natVar("x"), natVar("x"));
        verify(mockZ3Client).isSat(programCode);
    }

    @Test
    public void checkReturnsTrueIfZ3ClientSaysNotSat() throws Exception {
        when(mockZ3Client.isSat(anyString())).thenReturn(false);
        boolean result = checker.check(natVar("x"), natVar("x"));
        assertThat(result).isTrue();
    }

    @Test
    public void checkReturnsFalseIfZ3ClientSaysSat() throws Exception {
        when(mockZ3Client.isSat(anyString())).thenReturn(true);
        boolean result = checker.check(natVar("x"), natVar("x"));
        assertThat(result).isFalse();
    }

    @Test
    public void checkGeneratesCodeForCorrectFormula() throws Exception {
        // (f(x, y) / g(B) + 1) * 4 = (((f(x, y) + g(B)) / g(B)) / 8) * 32

        Multiplication t1 = mul(add(div(fun("f", natVar("x"), natVar("y")), fun("g", con("B"))), num(1)), num(4));

        Multiplication t2 = mul(
                div(add(fun("f", natVar("x"), natVar("y")), fun("g", con("B"))), fun("g", con("B")), num(8)),
                num(32));

        // Due to Set nature of quantified variables, could appear in either order...
        Formula f1 = not(forall(eq(t1, t2), natVar("x"), natVar("y")));
        Formula f2 = not(forall(eq(t1, t2), natVar("y"), natVar("x")));

        checker.check(t1, t2);

        ArgumentCaptor<Formula> formulaArgumentCaptor = ArgumentCaptor.forClass(Formula.class);
        verify(mockCodeGenerator).generateCheckSatCode(formulaArgumentCaptor.capture());

        Formula calledFormula = formulaArgumentCaptor.getValue();
        assertThat(calledFormula).has(new ContainedInCondition<>(f1, f2));
    }

}

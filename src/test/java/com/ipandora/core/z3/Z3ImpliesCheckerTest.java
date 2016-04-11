package com.ipandora.core.z3;

import com.ipandora.api.predicate.formula.*;
import com.ipandora.api.predicate.term.Variable;
import com.ipandora.core.formula.FormulaReducer;
import com.ipandora.core.formula.ImpliesCheckerException;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.mockito.Mock;
import org.mockito.runners.MockitoJUnitRunner;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.assertj.core.api.Assertions.assertThat;
import static org.mockito.Matchers.any;
import static org.mockito.Matchers.anyString;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

@RunWith(MockitoJUnitRunner.class)
public class Z3ImpliesCheckerTest {

    @Mock
    private SMTCodeGenerator mockCodeGenerator;

    @Mock
    private Z3Client mockZ3Client;

    @Mock
    private FormulaReducer mockConjunctor;

    private Z3ImpliesChecker checker;

    @Before
    public void setup() {
        checker = new Z3ImpliesChecker(mockCodeGenerator, mockZ3Client, mockConjunctor);
    }

    @Test(expected = ImpliesCheckerException.class)
    public void checkThrowsImpliesCheckerExceptionIfGivenNoAssumptions() throws Exception {
        checker.check(Collections.<Formula>emptyList(), new TruthFormula());
    }

    @Test
    public void checkReducesGivenAssumptions() throws Exception {
        AndFormula andFormula = new AndFormula(
                new PredicateFormula("Foo", Collections.singletonList(new Variable("x"))), new TruthFormula());
        FalsityFormula falsityFormula = new FalsityFormula();

        List<Formula> assumptions = Arrays.asList(andFormula, falsityFormula);

        checker.check(assumptions, new TruthFormula());
        verify(mockConjunctor).reduce(assumptions);
    }

    @Test
    public void checkCallsZ3ClientWithGeneratedCode() throws Exception {
        String programCode = "generated-code";

        when(mockCodeGenerator.generateCheckSatCode(any(Formula.class)))
                .thenReturn(programCode);

        checker.check(Collections.<Formula>singletonList(new FalsityFormula()), new TruthFormula());
        verify(mockZ3Client).isSat(programCode);
    }

    @Test
    public void checkReturnsTrueIfZ3ClientSaysNotSat() throws Exception {
        when(mockZ3Client.isSat(anyString())).thenReturn(false);
        boolean result = checker.check(Collections.<Formula>singletonList(new FalsityFormula()), new TruthFormula());
        assertThat(result).isTrue();
    }

    @Test
    public void checkReturnsFalseIfZ3ClientSaysSat() throws Exception {
        when(mockZ3Client.isSat(anyString())).thenReturn(true);
        boolean result = checker.check(Collections.<Formula>singletonList(new FalsityFormula()), new TruthFormula());
        assertThat(result).isFalse();
    }

}

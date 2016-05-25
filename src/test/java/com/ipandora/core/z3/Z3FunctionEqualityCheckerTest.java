package com.ipandora.core.z3;

import com.ipandora.api.predicate.formula.AndFormula;
import com.ipandora.api.predicate.formula.ForallFormula;
import com.ipandora.api.predicate.formula.Formula;
import com.ipandora.api.predicate.function.FunctionDefinition;
import com.ipandora.api.predicate.function.MathematicalFunctionDefinition;
import com.ipandora.core.function.FunctionDefinitionEncoder;
import com.ipandora.core.proof.ProofStepCheckException;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.mockito.Mock;
import org.mockito.runners.MockitoJUnitRunner;

import java.util.Arrays;
import java.util.Collections;

import static com.ipandora.testutils.FormulaCreators.*;
import static com.ipandora.testutils.FunctionCreators.funCase;
import static com.ipandora.testutils.FunctionCreators.mathFun;
import static com.ipandora.testutils.TermCreators.*;
import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.core.api.Assertions.fail;
import static org.mockito.Matchers.any;
import static org.mockito.Matchers.anyString;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

@RunWith(MockitoJUnitRunner.class)
public class Z3FunctionEqualityCheckerTest {

    @Mock
    private SMTCodeGenerator mockCodeGenerator;

    @Mock
    private Z3Client mockZ3Client;

    @Mock
    private FunctionDefinitionEncoder mockEncoder;

    private Z3FunctionEqualityChecker checker;

    @Before
    public void before() {
        checker = new Z3FunctionEqualityChecker(mockCodeGenerator, mockZ3Client, mockEncoder);

        when(mockEncoder.encode(any(FunctionDefinition.class)))
                .thenReturn(forall(truth(), natVar("x")));
    }

    @Test
    public void checkShouldCallEncodeWithFunctionDefinition() throws ProofStepCheckException {
        MathematicalFunctionDefinition f = mathFun("f", Collections.singletonList(natVar("x")),
                Collections.singletonList(funCase(add(natVar("x"), num(1)), truth())));

        checker.check(fun("f", natVar("x")), add(natVar("x"), num(1)), f);
        verify(mockEncoder).encode(f);
    }

    @Test
    public void checkShouldCallGenerateCodeWithCorrectFormula() throws Exception {
        MathematicalFunctionDefinition f = mathFun("f", Arrays.asList(natVar("x"), natVar("y")),
                Collections.singletonList(funCase(add(natVar("x"), natVar("y")), truth())));

        when(mockEncoder.encode(f))
                .thenReturn(forall(truth(), natVar("x"), natVar("y")));

        checker.check(fun("f", natVar("x"), natVar("y")), add(natVar("x"), natVar("y")), f);

        // mockEncoder setup to return truth
        AndFormula and = and(truth(), not(eq(fun("f", natVar("x"), natVar("y")), add(natVar("x"), natVar("y")))));
        ForallFormula expected = forall(and, natVar("x"), natVar("y"));

        verify(mockCodeGenerator).generateCheckSatCode(expected);
    }

    @Test
    public void checkThrowsProofStepExceptionWithMessageIfCodeGeneratorThrows() throws Exception {
        MathematicalFunctionDefinition f = mathFun("f", Collections.singletonList(natVar("x")),
                Collections.singletonList(funCase(add(natVar("x"), num(1)), truth())));

        when(mockCodeGenerator.generateCheckSatCode(any(Formula.class)))
                .thenThrow(new Z3InvalidProblemException("test-message"));

        try {
            checker.check(fun("f", natVar("x")), add(natVar("x"), num(1)), f);
            fail("ProofStepException should have been thrown!");
        } catch (ProofStepCheckException e) {
            assertThat(e.getMessage()).isEqualTo("test-message");
        }
    }

    @Test
    public void checkShouldCallZ3ClientWithCorrectProgram() throws Exception {
        MathematicalFunctionDefinition f = mathFun("f", Collections.singletonList(natVar("x")),
                Collections.singletonList(funCase(add(natVar("x"), num(1)), truth())));

        when(mockCodeGenerator.generateCheckSatCode(any(Formula.class)))
                .thenReturn("program-code");

        checker.check(num(0), num(1), f);
        verify(mockZ3Client).isSat("program-code");
    }

    @Test
    public void checkShouldReturnNegationOfClientResponse() throws Exception {
        MathematicalFunctionDefinition f = mathFun("f", Collections.singletonList(natVar("x")),
                Collections.singletonList(funCase(add(natVar("x"), num(1)), truth())));

        when(mockZ3Client.isSat(anyString())).thenReturn(true);
        boolean result = checker.check(num(0), num(1), f);
        assertThat(result).isFalse();

        when(mockZ3Client.isSat(anyString())).thenReturn(false);
        result = checker.check(num(0), num(1), f);
        assertThat(result).isTrue();
    }

    @Test
    public void checkThrowsProofStepExceptionWithMessageIfZ3ClientThrowsUnknownException() throws Exception {
        MathematicalFunctionDefinition f = mathFun("f", Collections.singletonList(natVar("x")),
                Collections.singletonList(funCase(add(natVar("x"), num(1)), truth())));

        when(mockZ3Client.isSat(anyString()))
                .thenThrow(new Z3UnknownException());

        try {
            checker.check(num(0), num(1), f);
            fail("ProofStepException should have been thrown!");
        } catch (ProofStepCheckException e) {
            assertThat(e.getMessage()).isEqualTo("Unable to determine validity of proof step");
        }
    }

}

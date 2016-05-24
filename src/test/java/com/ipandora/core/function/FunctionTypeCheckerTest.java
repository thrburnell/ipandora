package com.ipandora.core.function;

import com.ipandora.api.predicate.formula.Formula;
import com.ipandora.api.predicate.function.MathematicalFunctionDefinition;
import com.ipandora.api.predicate.term.Term;
import com.ipandora.api.predicate.term.TypeMismatchException;
import com.ipandora.api.predicate.term.Variable;
import com.ipandora.core.formula.FormulaTypeChecker;
import com.ipandora.core.term.TermTypeChecker;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.mockito.Mock;
import org.mockito.runners.MockitoJUnitRunner;

import java.util.Arrays;
import java.util.Collections;

import static com.ipandora.testutils.FormulaCreators.eq;
import static com.ipandora.testutils.FormulaCreators.truth;
import static com.ipandora.testutils.FunctionCreators.*;
import static com.ipandora.testutils.TermCreators.*;
import static org.mockito.Matchers.any;
import static org.mockito.Mockito.doThrow;
import static org.mockito.Mockito.verify;

@RunWith(MockitoJUnitRunner.class)
public class FunctionTypeCheckerTest {

    private static final Variable N = Variable.withTypeNat("n");
    private static final MathematicalFunctionDefinition SUM_FN = mathFun("Sum", Collections.singletonList(N), Arrays.asList(
            funCase(num(0), ifCond(eq(N, num(0)))),
            funCase(add(N, fun("Sum", sub(N, num(1)))), otherCond())));

    @Mock
    private TermTypeChecker mockTermTypeChecker;

    @Mock
    private FormulaTypeChecker mockFormulaTypeChecker;

    private FunctionTypeChecker typeChecker;

    @Before
    public void before() {
        typeChecker = new FunctionTypeChecker(mockTermTypeChecker, mockFormulaTypeChecker);
    }

    @Test
    public void analyseShouldAskTermTypeCheckerForExpressionInEachCase() throws TypeMismatchException {
        typeChecker.analyse(SUM_FN);
        verify(mockTermTypeChecker).analyse(num(0));
        verify(mockTermTypeChecker).analyse(add(N, fun("Sum", sub(N, num(1)))));
    }

    @Test
    public void analyseShouldAskFormulaTypeCheckerForConditionFormulaInEachCase() throws TypeMismatchException {
        typeChecker.analyse(SUM_FN);
        verify(mockFormulaTypeChecker).analyse(eq(N, num(0)));
        verify(mockFormulaTypeChecker).analyse(truth());
    }

    @Test(expected = TypeMismatchException.class)
    public void analyseShouldPropagateTermTypeCheckerException() throws TypeMismatchException {
        doThrow(new TypeMismatchException("test")).when(mockTermTypeChecker).analyse(any(Term.class));
        typeChecker.analyse(SUM_FN);
    }

    @Test(expected = TypeMismatchException.class)
    public void analyseShouldPropagateFormulaTypeCheckerException() throws TypeMismatchException {
        doThrow(new TypeMismatchException("test")).when(mockFormulaTypeChecker).analyse(any(Formula.class));
        typeChecker.analyse(SUM_FN);
    }

    @Test(expected = TypeMismatchException.class)
    public void analyseShouldThrowIfExpressionReturnTypeIsNotNat() throws TypeMismatchException {
        MathematicalFunctionDefinition fn = mathFun("Sum", Collections.singletonList(N), Arrays.asList(
                funCase(con("c"), ifCond(eq(N, num(0)))),
                funCase(add(N, fun("Sum", sub(N, num(1)))), otherCond())));

        typeChecker.analyse(fn);
    }

}
package com.ipandora.core.formula;

import com.ipandora.api.predicate.formula.*;
import com.ipandora.api.predicate.term.*;
import com.ipandora.api.predicate.term.Number;
import com.ipandora.core.term.TermTypeChecker;
import com.ipandora.core.util.WrappingRuntimeException;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.mockito.Mock;
import org.mockito.runners.MockitoJUnitRunner;

import java.util.Arrays;

import static org.assertj.core.api.Assertions.fail;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

@RunWith(MockitoJUnitRunner.class)
public class FormulaTypeCheckerTest {

    @Mock
    private TermTypeChecker mockTermTypeChecker;

    private FormulaTypeChecker typeChecker;

    @Before
    public void before() {
        typeChecker = new FormulaTypeChecker(mockTermTypeChecker);
    }


    @Test
    public void analyseShouldAskTermTypeCheckerForEachParamOfPredicate() {
        Number number = new Number(1);
        Constant constant = new Constant("y");
        Variable variable = new Variable("?x");
        PredicateFormula predicate = new PredicateFormula("Foo", Arrays.<Term>asList(number, constant, variable));

        typeChecker.analyse(predicate);

        verify(mockTermTypeChecker).visit(number);
        verify(mockTermTypeChecker).visit(constant);
        verify(mockTermTypeChecker).visit(variable);
    }

    @Test
    public void analyseShouldAskTermTypeCheckerForEachParamOfEqual() {
        Number number = new Number(2);
        Variable variable = Variable.withTypeNat("?x");
        EqualToFormula equalToFormula = new EqualToFormula(number, variable);

        typeChecker.analyse(equalToFormula);

        verify(mockTermTypeChecker).visit(number);
        verify(mockTermTypeChecker).visit(variable);
    }

    @Test
    public void analyseShouldAskTermTypeCheckerForEachParamOfGreaterThan() {
        Number number = new Number(2);
        Variable variable = Variable.withTypeNat("?x");
        GreaterThanFormula greaterThanFormula = new GreaterThanFormula(number, variable);

        typeChecker.analyse(greaterThanFormula);

        verify(mockTermTypeChecker).visit(number);
        verify(mockTermTypeChecker).visit(variable);
    }

    @Test
    public void analyseShouldAskTermTypeCheckerForEachParamOfGreaterThanEqual() {
        Number number = new Number(2);
        Variable variable = Variable.withTypeNat("?x");
        GreaterThanEqualFormula greaterThanEqualFormula = new GreaterThanEqualFormula(number, variable);

        typeChecker.analyse(greaterThanEqualFormula);

        verify(mockTermTypeChecker).visit(number);
        verify(mockTermTypeChecker).visit(variable);
    }

    @Test
    public void analyseShouldAskTermTypeCheckerForEachParamOfLessThan() {
        Number number = new Number(2);
        Variable variable = Variable.withTypeNat("?x");
        LessThanFormula lessThanFormula = new LessThanFormula(number, variable);

        typeChecker.analyse(lessThanFormula);

        verify(mockTermTypeChecker).visit(number);
        verify(mockTermTypeChecker).visit(variable);
    }

    @Test
    public void analyseShouldAskTermTypeCheckerForEachParamOfLessThanEqual() {
        Number number = new Number(2);
        Variable variable = Variable.withTypeNat("?x");
        LessThanEqualFormula lessThanEqualFormula = new LessThanEqualFormula(number, variable);

        typeChecker.analyse(lessThanEqualFormula);

        verify(mockTermTypeChecker).visit(number);
        verify(mockTermTypeChecker).visit(variable);
    }

    @Test(expected = TypeMismatchException.class)
    public void analyseShouldPropagateTermTypeCheckerException() throws Exception {
        Addition addition = new Addition(new Variable("?x"), Variable.withTypeNat("?y"));
        EqualToFormula equalToFormula = new EqualToFormula(addition, new Number(2));

        when(mockTermTypeChecker.visit(addition))
                .thenThrow(new WrappingRuntimeException(new TypeMismatchException("Test")));

        analyseAndExpectWrappedRuntimeException(equalToFormula);
    }

    @Test(expected = TypeMismatchException.class)
    public void analyseShouldThrowIfEqualComparesUntypedTerm() throws Exception {
        Number number = new Number(2);
        Variable variable = new Variable("?x");
        EqualToFormula equalToFormula = new EqualToFormula(number, variable);

        analyseAndExpectWrappedRuntimeException(equalToFormula);
    }

    @Test(expected = TypeMismatchException.class)
    public void analyseShouldThrowIfGreaterThanComparesUntypedTerm() throws Exception {
        Number number = new Number(2);
        Variable variable = new Variable("?x");
        GreaterThanFormula greaterThanFormula = new GreaterThanFormula(number, variable);

        analyseAndExpectWrappedRuntimeException(greaterThanFormula);
    }

    @Test(expected = TypeMismatchException.class)
    public void analyseShouldThrowIfGreaterThanEqualComparesUntypedTerm() throws Exception {
        Number number = new Number(2);
        Variable variable = new Variable("?x");
        GreaterThanEqualFormula greaterThanEqualFormula = new GreaterThanEqualFormula(number, variable);

        analyseAndExpectWrappedRuntimeException(greaterThanEqualFormula);
    }

    @Test(expected = TypeMismatchException.class)
    public void analyseShouldThrowIfLessThanComparesUntypedTerm() throws Exception {
        Number number = new Number(2);
        Variable variable = new Variable("?x");
        LessThanFormula lessThanFormula = new LessThanFormula(number, variable);

        analyseAndExpectWrappedRuntimeException(lessThanFormula);
    }

    @Test(expected = TypeMismatchException.class)
    public void analyseShouldThrowIfLessThanEqualComparesUntypedTerm() throws Exception {
        Number number = new Number(2);
        Variable variable = new Variable("?x");
        LessThanEqualFormula lessThanEqualFormula = new LessThanEqualFormula(number, variable);

        analyseAndExpectWrappedRuntimeException(lessThanEqualFormula);
    }

    private void analyseAndExpectWrappedRuntimeException(Formula formula) throws Exception {
        try {
            typeChecker.analyse(formula);
        } catch (WrappingRuntimeException e) {
            throw e.getWrappedException();
        }

        fail("WrappingRuntimeException should have been thrown!");
    }

}
package com.ipandora.core.term;

import com.ipandora.api.predicate.term.*;
import com.ipandora.api.predicate.term.Number;
import com.ipandora.core.util.WrappingRuntimeException;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;

import static org.assertj.core.api.Assertions.fail;

public class TermTypeCheckerTest {

    private final TermTypeChecker termTypeChecker = new TermTypeChecker();

    // Addition

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForAdditionWithConstant() throws Exception {
        Addition addition = new Addition(Variable.withTypeNat("?x"), new Constant("y"));
        visitAndExpectWrappedRuntimeException(addition);
    }

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForAdditionWithUntypedVariable() throws Exception {
        Addition addition = new Addition(new Variable("?x"), Variable.withTypeNat("?y"));
        visitAndExpectWrappedRuntimeException(addition);
    }

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForAdditionWithUntypedFunction() throws Exception {
        Addition addition = new Addition(
                new Function("Foo", Collections.<Term>singletonList(new Number(1))),
                Variable.withTypeNat("?x"));

        visitAndExpectWrappedRuntimeException(addition);
    }

    @Test
    public void visitShouldNotThrowForAdditionWithNatVariables() {
        Addition addition = new Addition(Variable.withTypeNat("?x"), Variable.withTypeNat("?y"));
        termTypeChecker.visit(addition);
    }

    // Subtraction

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForSubtractionWithConstant() throws Exception {
        Subtraction subtraction = new Subtraction(Variable.withTypeNat("?x"), new Constant("y"));
        visitAndExpectWrappedRuntimeException(subtraction);
    }

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForSubtractionWithUntypedVariable() throws Exception {
        Subtraction subtraction = new Subtraction(new Variable("?x"), Variable.withTypeNat("?y"));
        visitAndExpectWrappedRuntimeException(subtraction);
    }

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForSubtractionWithUntypedFunction() throws Exception {
        Subtraction subtraction = new Subtraction(
                new Function("Foo", Collections.<Term>singletonList(new Number(1))),
                Variable.withTypeNat("?x"));

        visitAndExpectWrappedRuntimeException(subtraction);
    }

    @Test
    public void visitShouldNotThrowForSubtractionWithNatVariables() {
        Subtraction subtraction = new Subtraction(Variable.withTypeNat("?x"), Variable.withTypeNat("?y"));
        termTypeChecker.visit(subtraction);
    }

    // Multiplication

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForMultiplicationWithConstant() throws Exception {
        Multiplication multiplication = new Multiplication(Variable.withTypeNat("?x"), new Constant("y"));
        visitAndExpectWrappedRuntimeException(multiplication);
    }

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForMultiplicationWithUntypedVariable() throws Exception {
        Multiplication multiplication = new Multiplication(new Variable("?x"), Variable.withTypeNat("?y"));
        visitAndExpectWrappedRuntimeException(multiplication);
    }

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForMultiplicationWithUntypedFunction() throws Exception {
        Multiplication multiplication = new Multiplication(
                new Function("Foo", Collections.<Term>singletonList(new Number(1))),
                Variable.withTypeNat("?x"));

        visitAndExpectWrappedRuntimeException(multiplication);
    }

    @Test
    public void visitShouldNotThrowForMultiplicationWithNatVariables() {
        Multiplication multiplication = new Multiplication(Variable.withTypeNat("?x"), Variable.withTypeNat("?y"));
        termTypeChecker.visit(multiplication);
    }

    // Division

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForDivisionWithConstant() throws Exception {
        Division division = new Division(Variable.withTypeNat("?x"), new Constant("y"));
        visitAndExpectWrappedRuntimeException(division);
    }

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForDivisionWithUntypedVariable() throws Exception {
        Division division = new Division(new Variable("?x"), Variable.withTypeNat("?y"));
        visitAndExpectWrappedRuntimeException(division);
    }

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForDivisionWithUntypedFunction() throws Exception {
        Division division = new Division(
                new Function("Foo", Collections.<Term>singletonList(new Number(1))),
                Variable.withTypeNat("?x"));

        visitAndExpectWrappedRuntimeException(division);
    }

    @Test
    public void visitShouldNotThrowForDivisionWithNatVariables() {
        Division division = new Division(Variable.withTypeNat("?x"), Variable.withTypeNat("?y"));
        termTypeChecker.visit(division);
    }


    // Power
    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForPowerWithConstant() throws Exception {
        Power power = new Power(new Constant("x"), 2);
        visitAndExpectWrappedRuntimeException(power);
    }

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForPowerWithUntypedVariable() throws Exception {
        Power power = new Power(new Variable("?x"), 3);
        visitAndExpectWrappedRuntimeException(power);
    }

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForPowerWithUntypedFunction() throws Exception {
        Power power = new Power(
                new Function("Foo", Collections.<Term>singletonList(new Number(1))),
                2);

        visitAndExpectWrappedRuntimeException(power);
    }

    @Test
    public void visitShouldNotThrowForPowerWithNatVariables() {
        Power power = new Power(Variable.withTypeNat("?x"), 3);
        termTypeChecker.visit(power);
    }

    // Function
    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForFunctionWithBadlyTypedParams() throws Exception {
        Function function = new Function("Foo",
                Arrays.asList(new Number(2), new Addition(new Number(1), new Variable("?x"))));

        visitAndExpectWrappedRuntimeException(function);
    }

    @Test
    public void visitShouldNotThrowForFunctionWithWellTypedParams() {
        Function function = new Function("Foo",
                Arrays.asList(new Number(2), new Multiplication(Variable.withTypeNat("?x"), new Number(3))));

        termTypeChecker.visit(function);
    }


    private void visitAndExpectWrappedRuntimeException(Term term) throws Exception {
        try {
            termTypeChecker.visit(term);
        } catch (WrappingRuntimeException e) {
            throw e.getWrappedException();
        }

        fail("WrappingRuntimeException should have been thrown!");
    }

}

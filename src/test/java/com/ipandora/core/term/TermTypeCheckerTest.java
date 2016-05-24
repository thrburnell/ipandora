package com.ipandora.core.term;

import com.ipandora.api.predicate.term.*;
import com.ipandora.api.predicate.term.Number;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;

public class TermTypeCheckerTest {

    private final TermTypeChecker termTypeChecker = new TermTypeChecker();

    // Addition

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForAdditionWithConstant() throws Exception {
        Addition addition = new Addition(Variable.withTypeNat("?x"), new Constant("y"));
        termTypeChecker.analyse(addition);
    }

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForAdditionWithUntypedVariable() throws Exception {
        Addition addition = new Addition(new Variable("?x"), Variable.withTypeNat("?y"));
        termTypeChecker.analyse(addition);
    }

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForAdditionWithUntypedFunction() throws Exception {
        Addition addition = new Addition(
                new Function("Foo", Collections.<Term>singletonList(new Number(1))),
                Variable.withTypeNat("?x"));

        termTypeChecker.analyse(addition);
    }

    @Test
    public void visitShouldNotThrowForAdditionWithNatVariables() throws TypeMismatchException {
        Addition addition = new Addition(Variable.withTypeNat("?x"), Variable.withTypeNat("?y"));
        termTypeChecker.analyse(addition);
    }

    // Subtraction

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForSubtractionWithConstant() throws Exception {
        Subtraction subtraction = new Subtraction(Variable.withTypeNat("?x"), new Constant("y"));
        termTypeChecker.analyse(subtraction);
    }

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForSubtractionWithUntypedVariable() throws Exception {
        Subtraction subtraction = new Subtraction(new Variable("?x"), Variable.withTypeNat("?y"));
        termTypeChecker.analyse(subtraction);
    }

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForSubtractionWithUntypedFunction() throws Exception {
        Subtraction subtraction = new Subtraction(
                new Function("Foo", Collections.<Term>singletonList(new Number(1))),
                Variable.withTypeNat("?x"));

        termTypeChecker.analyse(subtraction);
    }

    @Test
    public void visitShouldNotThrowForSubtractionWithNatVariables() throws TypeMismatchException {
        Subtraction subtraction = new Subtraction(Variable.withTypeNat("?x"), Variable.withTypeNat("?y"));
        termTypeChecker.analyse(subtraction);
    }

    // Multiplication

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForMultiplicationWithConstant() throws Exception {
        Multiplication multiplication = new Multiplication(Variable.withTypeNat("?x"), new Constant("y"));
        termTypeChecker.analyse(multiplication);
    }

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForMultiplicationWithUntypedVariable() throws Exception {
        Multiplication multiplication = new Multiplication(new Variable("?x"), Variable.withTypeNat("?y"));
        termTypeChecker.analyse(multiplication);
    }

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForMultiplicationWithUntypedFunction() throws Exception {
        Multiplication multiplication = new Multiplication(
                new Function("Foo", Collections.<Term>singletonList(new Number(1))),
                Variable.withTypeNat("?x"));

        termTypeChecker.analyse(multiplication);
    }

    @Test
    public void visitShouldNotThrowForMultiplicationWithNatVariables() throws TypeMismatchException {
        Multiplication multiplication = new Multiplication(Variable.withTypeNat("?x"), Variable.withTypeNat("?y"));
        termTypeChecker.analyse(multiplication);
    }

    // Division

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForDivisionWithConstant() throws Exception {
        Division division = new Division(Variable.withTypeNat("?x"), new Constant("y"));
        termTypeChecker.analyse(division);
    }

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForDivisionWithUntypedVariable() throws Exception {
        Division division = new Division(new Variable("?x"), Variable.withTypeNat("?y"));
        termTypeChecker.analyse(division);
    }

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForDivisionWithUntypedFunction() throws Exception {
        Division division = new Division(
                new Function("Foo", Collections.<Term>singletonList(new Number(1))),
                Variable.withTypeNat("?x"));

        termTypeChecker.analyse(division);
    }

    @Test
    public void visitShouldNotThrowForDivisionWithNatVariables() throws TypeMismatchException {
        Division division = new Division(Variable.withTypeNat("?x"), Variable.withTypeNat("?y"));
        termTypeChecker.analyse(division);
    }


    // Power
    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForPowerWithConstant() throws Exception {
        Power power = new Power(new Constant("x"), 2);
        termTypeChecker.analyse(power);
    }

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForPowerWithUntypedVariable() throws Exception {
        Power power = new Power(new Variable("?x"), 3);
        termTypeChecker.analyse(power);
    }

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForPowerWithUntypedFunction() throws Exception {
        Power power = new Power(
                new Function("Foo", Collections.<Term>singletonList(new Number(1))),
                2);

        termTypeChecker.analyse(power);
    }

    @Test
    public void visitShouldNotThrowForPowerWithNatVariables() throws TypeMismatchException {
        Power power = new Power(Variable.withTypeNat("?x"), 3);
        termTypeChecker.analyse(power);
    }

    // Function
    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForFunctionWithBadlyTypedParams() throws Exception {
        Function function = new Function("Foo",
                Arrays.asList(new Number(2), new Addition(new Number(1), new Variable("?x"))));

        termTypeChecker.analyse(function);
    }

    @Test
    public void visitShouldNotThrowForFunctionWithWellTypedParams() throws TypeMismatchException {
        Function function = new Function("Foo",
                Arrays.asList(new Number(2), new Multiplication(Variable.withTypeNat("?x"), new Number(3))));

        termTypeChecker.analyse(function);
    }

}

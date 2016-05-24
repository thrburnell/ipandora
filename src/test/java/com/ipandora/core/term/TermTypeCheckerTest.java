package com.ipandora.core.term;

import com.ipandora.api.predicate.function.FunctionPrototype;
import com.ipandora.api.predicate.term.*;
import com.ipandora.api.predicate.term.Number;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

public class TermTypeCheckerTest {

    private static final List<FunctionPrototype> EMPTY_LIST = Collections.emptyList();
    private static final FunctionPrototype FOO_PROTOTYPE = new FunctionPrototype("Foo", Collections.singletonList(Type.NAT), Type.NAT);
    private final TermTypeChecker termTypeChecker = new TermTypeChecker();

    // Addition

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForAdditionWithConstant() throws Exception {
        Addition addition = new Addition(Variable.withTypeNat("?x"), new Constant("y"));
        termTypeChecker.analyse(addition, EMPTY_LIST);
    }

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForAdditionWithUntypedVariable() throws Exception {
        Addition addition = new Addition(new Variable("?x"), Variable.withTypeNat("?y"));
        termTypeChecker.analyse(addition, EMPTY_LIST);
    }

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForAdditionWithUntypedFunction() throws Exception {
        Addition addition = new Addition(
                new Function("Foo", Collections.<Term>singletonList(new Number(1))),
                Variable.withTypeNat("?x"));

        termTypeChecker.analyse(addition, EMPTY_LIST);
    }

    @Test
    public void visitShouldNotThrowForAdditionWithNatVariables() throws TypeMismatchException {
        Addition addition = new Addition(Variable.withTypeNat("?x"), Variable.withTypeNat("?y"));
        termTypeChecker.analyse(addition, EMPTY_LIST);
    }

    // Subtraction

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForSubtractionWithConstant() throws Exception {
        Subtraction subtraction = new Subtraction(Variable.withTypeNat("?x"), new Constant("y"));
        termTypeChecker.analyse(subtraction, EMPTY_LIST);
    }

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForSubtractionWithUntypedVariable() throws Exception {
        Subtraction subtraction = new Subtraction(new Variable("?x"), Variable.withTypeNat("?y"));
        termTypeChecker.analyse(subtraction, EMPTY_LIST);
    }

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForSubtractionWithUntypedFunction() throws Exception {
        Subtraction subtraction = new Subtraction(
                new Function("Foo", Collections.<Term>singletonList(new Number(1))),
                Variable.withTypeNat("?x"));

        termTypeChecker.analyse(subtraction, EMPTY_LIST);
    }

    @Test
    public void visitShouldNotThrowForSubtractionWithNatVariables() throws TypeMismatchException {
        Subtraction subtraction = new Subtraction(Variable.withTypeNat("?x"), Variable.withTypeNat("?y"));
        termTypeChecker.analyse(subtraction, EMPTY_LIST);
    }

    // Multiplication

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForMultiplicationWithConstant() throws Exception {
        Multiplication multiplication = new Multiplication(Variable.withTypeNat("?x"), new Constant("y"));
        termTypeChecker.analyse(multiplication, EMPTY_LIST);
    }

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForMultiplicationWithUntypedVariable() throws Exception {
        Multiplication multiplication = new Multiplication(new Variable("?x"), Variable.withTypeNat("?y"));
        termTypeChecker.analyse(multiplication, EMPTY_LIST);
    }

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForMultiplicationWithUntypedFunction() throws Exception {
        Multiplication multiplication = new Multiplication(
                new Function("Foo", Collections.<Term>singletonList(new Number(1))),
                Variable.withTypeNat("?x"));

        termTypeChecker.analyse(multiplication, EMPTY_LIST);
    }

    @Test
    public void visitShouldNotThrowForMultiplicationWithNatVariables() throws TypeMismatchException {
        Multiplication multiplication = new Multiplication(Variable.withTypeNat("?x"), Variable.withTypeNat("?y"));
        termTypeChecker.analyse(multiplication, EMPTY_LIST);
    }

    // Division

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForDivisionWithConstant() throws Exception {
        Division division = new Division(Variable.withTypeNat("?x"), new Constant("y"));
        termTypeChecker.analyse(division, EMPTY_LIST);
    }

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForDivisionWithUntypedVariable() throws Exception {
        Division division = new Division(new Variable("?x"), Variable.withTypeNat("?y"));
        termTypeChecker.analyse(division, EMPTY_LIST);
    }

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForDivisionWithUntypedFunction() throws Exception {
        Division division = new Division(
                new Function("Foo", Collections.<Term>singletonList(new Number(1))),
                Variable.withTypeNat("?x"));

        termTypeChecker.analyse(division, EMPTY_LIST);
    }

    @Test
    public void visitShouldNotThrowForDivisionWithNatVariables() throws TypeMismatchException {
        Division division = new Division(Variable.withTypeNat("?x"), Variable.withTypeNat("?y"));
        termTypeChecker.analyse(division, EMPTY_LIST);
    }


    // Power
    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForPowerWithConstant() throws Exception {
        Power power = new Power(new Constant("x"), 2);
        termTypeChecker.analyse(power, EMPTY_LIST);
    }

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForPowerWithUntypedVariable() throws Exception {
        Power power = new Power(new Variable("?x"), 3);
        termTypeChecker.analyse(power, EMPTY_LIST);
    }

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForPowerWithUntypedFunction() throws Exception {

        Power power = new Power(
                new Function("Foo", Collections.<Term>singletonList(new Number(1))),
                2);

        termTypeChecker.analyse(power, Collections.singletonList(FOO_PROTOTYPE));
    }

    @Test
    public void visitShouldNotThrowForPowerWithNatVariables() throws TypeMismatchException {
        Power power = new Power(Variable.withTypeNat("?x"), 3);
        termTypeChecker.analyse(power, EMPTY_LIST);
    }

    // Function
    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowForFunctionWithBadlyTypedParams() throws Exception {
        Function function = new Function("Foo",
                Arrays.asList(new Number(2), new Addition(new Number(1), new Variable("?x"))));

        termTypeChecker.analyse(function, Collections.singletonList(FOO_PROTOTYPE));
    }

    @Test(expected = TypeMismatchException.class)
    public void visitShouldThrowIfFunctionNotKnown() throws TypeMismatchException {
        Function function = new Function("Bar",
                Arrays.asList(new Number(2), new Addition(new Number(1), new Variable("?x"))));

        Addition addition = new Addition(function, new Number(2));

        termTypeChecker.analyse(addition, Collections.singletonList(FOO_PROTOTYPE));
    }

    @Test(expected = TypeMismatchException.class)
    public void visitWithPrototypesShouldThrowIfFunctionHasDifferentReturnType() throws TypeMismatchException {
        Function function = new Function("Foo", Collections.<Term>singletonList(new Number(2)));
        Addition addition = new Addition(function, new Number(2));

        termTypeChecker.analyse(addition, Collections.singletonList(FOO_PROTOTYPE));
    }

    @Test(expected = TypeMismatchException.class)
    public void visitWithPrototypesShouldThrowIfFunctionHasDifferentArgCount() throws TypeMismatchException {
        Function function = new Function("Foo", Arrays.<Term>asList(new Number(2), new Number(1)), Type.NAT);
        Addition addition = new Addition(function, new Number(2));

        termTypeChecker.analyse(addition, Collections.singletonList(FOO_PROTOTYPE));
    }

    @Test(expected = TypeMismatchException.class)
    public void visitWithPrototypesShouldThrowIfFunctionHasDifferentArgTypes() throws TypeMismatchException {
        Function function = new Function("Foo", Collections.<Term>singletonList(new Constant("x")), Type.NAT);
        Addition addition = new Addition(function, new Number(2));

        termTypeChecker.analyse(addition, Collections.singletonList(FOO_PROTOTYPE));
    }

    @Test(expected = TypeMismatchException.class)
    public void visitWithPrototypesShouldThrowIfMultiplePrototypesGivenForSameFunctionName()
            throws TypeMismatchException {

        FunctionPrototype foo1 = new FunctionPrototype("Foo", Collections.singletonList(Type.NAT), Type.NAT);
        FunctionPrototype foo2 = new FunctionPrototype("Foo", Collections.singletonList(Type.UNKNOWN), Type.NAT);

        termTypeChecker.analyse(new Number(1), Arrays.asList(foo1, foo2));
    }

}

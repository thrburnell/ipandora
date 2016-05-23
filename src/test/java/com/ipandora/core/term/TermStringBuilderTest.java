package com.ipandora.core.term;

import com.ipandora.api.predicate.term.*;
import com.ipandora.api.predicate.term.Number;
import org.junit.Test;

import java.util.Arrays;

import static org.assertj.core.api.Assertions.assertThat;

public class TermStringBuilderTest {

    private static final Variable X = new Variable("x");
    private static final Variable Y = new Variable("y");
    private static final Variable Z = new Variable("z");

    @Test
    public void buildConstant() {
        TermStringBuilder builder = new TermStringBuilder();
        Constant term = new Constant("k");
        String result = builder.build(term);
        assertThat(result).isEqualTo("k");
    }

    @Test
    public void buildVariable() {
        TermStringBuilder builder = new TermStringBuilder();
        Variable term = new Variable("?x");
        String result = builder.build(term);
        assertThat(result).isEqualTo("?x");
    }

    @Test
    public void buildDivideEqualToMultiplySoBrackets() {
        TermStringBuilder builder = new TermStringBuilder();
        // (x * y) / z
        Term term = new Division(new Multiplication(X, Y), Z);
        String result = builder.build(term);
        assertThat(result).isEqualTo("(x * y) / z");

        // x * (y / z)
        term = new Multiplication(X, new Division(Y, Z));
        result = builder.build(term);
        assertThat(result).isEqualTo("x * (y / z)");

        // (x / y) * z
        term = new Multiplication(new Division(X, Y), Z);
        result = builder.build(term);
        assertThat(result).isEqualTo("(x / y) * z");

        // x / (y * z)
        term = new Division(X, new Multiplication(Y, Z));
        result = builder.build(term);
        assertThat(result).isEqualTo("x / (y * z)");
    }

    @Test
    public void buildMultiplyStrongerThanPlusSoNoBrackets() {
        // x * y + z
        TermStringBuilder builder = new TermStringBuilder();
        Addition term = new Addition(new Multiplication(X, Y), Z);
        String result = builder.build(term);
        assertThat(result).isEqualTo("x * y + z");
    }

    @Test
    public void buildMultiplyStrongerThanPlusSoBrackets() {
        // x * (y + z)
        TermStringBuilder builder = new TermStringBuilder();
        Multiplication term = new Multiplication(X, new Addition(Y, Z));
        String result = builder.build(term);
        assertThat(result).isEqualTo("x * (y + z)");
    }

    @Test
    public void buildDivisionStrongerThanPlusSoNoBrackets() {
        // x / y + z
        TermStringBuilder builder = new TermStringBuilder();
        Addition term = new Addition(new Division(X, Y), Z);
        String result = builder.build(term);
        assertThat(result).isEqualTo("x / y + z");
    }

    @Test
    public void buildDivisionStrongerThanPlusSoBrackets() {
        // x / (y + z)
        TermStringBuilder builder = new TermStringBuilder();
        Division term = new Division(X, new Addition(Y, Z));
        String result = builder.build(term);
        assertThat(result).isEqualTo("x / (y + z)");
    }

    @Test
    public void buildPlusEqualToMinusSoNoBrackets() {
        // x + y - z
        TermStringBuilder builder = new TermStringBuilder();
        Term term = new Addition(X, new Subtraction(Y, Z));
        String result = builder.build(term);
        assertThat(result).isEqualTo("x + y - z");

        term = new Subtraction(new Addition(X, Y), Z);
        result = builder.build(term);
        assertThat(result).isEqualTo("x + y - z");
    }

    @Test
    public void buildMinusStrongerThanPlusSoNoBrackets() {
        // x - y + z
        TermStringBuilder builder = new TermStringBuilder();
        Addition term = new Addition(new Subtraction(X, Y), Z);
        String result = builder.build(term);
        assertThat(result).isEqualTo("x - y + z");
    }

    @Test
    public void buildMinusStrongerThanPlusSoBrackets() {
        // x - (y + z)
        TermStringBuilder builder = new TermStringBuilder();
        Subtraction term = new Subtraction(X, new Addition(Y, Z));
        String result = builder.build(term);
        assertThat(result).isEqualTo("x - (y + z)");
    }

    @Test
    public void buildNumber() {
        TermStringBuilder builder = new TermStringBuilder();
        Number term = new Number(3);
        String result = builder.build(term);
        assertThat(result).isEqualTo("3");
    }

    @Test
    public void buildFunction() {
        // Foo(x, y, 2)
        TermStringBuilder builder = new TermStringBuilder();
        Function term = new Function("Foo", Arrays.<Term>asList(X, Y, new Number(2)));
        String result = builder.build(term);
        assertThat(result).isEqualTo("Foo(x, y, 2)");
    }

    @Test
    public void buildPower() {
        // 2^3
        TermStringBuilder builder = new TermStringBuilder();
        Power term = new Power(new Number(2), 3);
        String result = builder.build(term);
        assertThat(result).isEqualTo("2^3");
    }

    @Test
    public void buildPowerStrongerThanMultiplySoNoBrackets() {
        // x * y^2
        TermStringBuilder builder = new TermStringBuilder();
        Multiplication term = new Multiplication(X, new Power(Y, 2));
        String result = builder.build(term);
        assertThat(result).isEqualTo("x * y^2");
    }

    @Test
    public void buildPowerStrongerThanMultiplySoBrackets() {
        // (x * y)^2
        TermStringBuilder builder = new TermStringBuilder();
        Power term = new Power(new Multiplication(X, Y), 2);
        String result = builder.build(term);
        assertThat(result).isEqualTo("(x * y)^2");
    }

    @Test
    public void buildPowerStrongerThanDivideSoNoBrackets() {
        // x / y^2
        TermStringBuilder builder = new TermStringBuilder();
        Division term = new Division(X, new Power(Y, 2));
        String result = builder.build(term);
        assertThat(result).isEqualTo("x / y^2");
    }

    @Test
    public void buildPowerStrongerThanDivideSoBrackets() {
        // (x / y)^2
        TermStringBuilder builder = new TermStringBuilder();
        Power term = new Power(new Division(X, Y), 2);
        String result = builder.build(term);
        assertThat(result).isEqualTo("(x / y)^2");
    }

    @Test
    public void buildNestedPlusShouldHaveNoBrackets() {
        // x + y + z
        TermStringBuilder builder = new TermStringBuilder();
        Addition term = new Addition(X, new Addition(Y, Z));
        String result = builder.build(term);
        assertThat(result).isEqualTo("x + y + z");

        term = new Addition(new Addition(X, Y), Z);
        result = builder.build(term);
        assertThat(result).isEqualTo("x + y + z");
    }

    @Test
    public void buildNestedMinusShouldHaveNoBrackets() {
        // x - y - z
        TermStringBuilder builder = new TermStringBuilder();
        Subtraction term = new Subtraction(X, new Subtraction(Y, Z));
        String result = builder.build(term);
        assertThat(result).isEqualTo("x - y - z");

        term = new Subtraction(new Subtraction(X, Y), Z);
        result = builder.build(term);
        assertThat(result).isEqualTo("x - y - z");
    }

    @Test
    public void buildNestedMultiplyShouldHaveNoBrackets() {
        // x * y * z
        TermStringBuilder builder = new TermStringBuilder();
        Multiplication term = new Multiplication(X, new Multiplication(Y, Z));
        String result = builder.build(term);
        assertThat(result).isEqualTo("x * y * z");

        term = new Multiplication(new Multiplication(X, Y), Z);
        result = builder.build(term);
        assertThat(result).isEqualTo("x * y * z");
    }

    @Test
    public void buildNestedDivideShouldHaveBrackets() {
        // x / (y / z)
        TermStringBuilder builder = new TermStringBuilder();
        Division term = new Division(X, new Division(Y, Z));
        String result = builder.build(term);
        assertThat(result).isEqualTo("x / (y / z)");

        term = new Division(new Division(X, Y), Z);
        result = builder.build(term);
        assertThat(result).isEqualTo("(x / y) / z");
    }

}

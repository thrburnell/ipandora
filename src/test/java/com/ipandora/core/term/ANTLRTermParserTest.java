package com.ipandora.core.term;

import com.ipandora.api.predicate.function.FunctionPrototype;
import com.ipandora.api.predicate.term.*;
import com.ipandora.api.predicate.term.Number;
import org.junit.Before;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.assertj.core.api.Assertions.assertThat;

public class ANTLRTermParserTest {

    private ANTLRTermParser parser;

    @Before
    public void before() {
        TermTypeChecker termTypeChecker = new TermTypeChecker();
        parser = new ANTLRTermParser(termTypeChecker);
    }

    @Test
    public void fromStringNumber() throws TermParsingException {
        Term term = parser.fromStringWithTypeChecking("1");
        Number expected = new Number(1);
        assertThat(term).isEqualTo(expected);
    }

    @Test
    public void fromStringConstant() throws TermParsingException {
        Term term = parser.fromStringWithTypeChecking("c");
        Constant expected = new Constant("c");
        assertThat(term).isEqualTo(expected);
    }

    @Test
    public void fromStringPlus() throws TermParsingException {
        Term term = parser.fromStringWithTypeChecking("1 + 2");
        Addition expected = new Addition(new Number(1), new Number(2));
        assertThat(term).isEqualTo(expected);
    }

    @Test
    public void fromStringMinus() throws TermParsingException {
        Term term = parser.fromStringWithTypeChecking("1 - 2");
        Subtraction expected = new Subtraction(new Number(1), new Number(2));
        assertThat(term).isEqualTo(expected);
    }

    @Test
    public void fromStringMultiply() throws TermParsingException {
        Term term = parser.fromStringWithTypeChecking("1 * 2");
        Multiplication expected = new Multiplication(new Number(1), new Number(2));
        assertThat(term).isEqualTo(expected);
    }

    @Test
    public void fromStringDivide() throws TermParsingException {
        Term term = parser.fromStringWithTypeChecking("1 / 2");
        Division expected = new Division(new Number(1), new Number(2));
        assertThat(term).isEqualTo(expected);
    }

    @Test
    public void fromStringPower() throws TermParsingException {
        Term term = parser.fromStringWithTypeChecking("1 ^ 2");
        Power expected = new Power(new Number(1), 2);
        assertThat(term).isEqualTo(expected);
    }

    @Test
    public void fromStringFunction() throws TermParsingException {
        Term term = parser.fromStringWithTypeChecking("Foo(x, 1)");
        Function expected = new Function("Foo", Arrays.<Term>asList(new Constant("x"), new Number(1)));
        assertThat(term).isEqualTo(expected);
    }

    @Test
    public void fromNestedPlus() throws TermParsingException {
        Term term = parser.fromStringWithTypeChecking("1 + 2 + 3");
        Addition expected = new Addition(new Addition(new Number(1), new Number(2)), new Number(3));
        assertThat(term).isEqualTo(expected);
    }

    @Test(expected = TermParsingException.class)
    public void fromStringShouldThrowIfInvalidTermGiven() throws TermParsingException {
        parser.fromStringWithTypeChecking("1 + 2 = 3");
    }

    @Test
    public void fromStringWithFunctionPrototypesShouldTypeFunctionTerm() throws TermParsingException {
        List<FunctionPrototype> prototypes = new ArrayList<>();
        prototypes.add(new FunctionPrototype("f", Collections.singletonList(Type.UNKNOWN), Type.NAT));

        Term term = parser.fromString("1 + f(x)", prototypes);
        Addition expected = new Addition(new Number(1),
                new Function("f", Collections.<Term>singletonList(new Constant("x")), Type.NAT));

        assertThat(term).isEqualTo(expected);
    }

}

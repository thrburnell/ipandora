package com.ipandora.core.term;

import com.ipandora.api.predicate.term.*;
import com.ipandora.api.predicate.term.Number;
import org.junit.Before;
import org.junit.Test;

import java.util.Arrays;

import static org.assertj.core.api.Assertions.assertThat;

public class ANTLRTermParserTest {

    private ANTLRTermParser parser;

    @Before
    public void before() {
        TermBuildingVisitor termBuildingVisitor = new TermBuildingVisitor(new SymbolTableCreator());
        TermTypeChecker termTypeChecker = new TermTypeChecker();
        parser = new ANTLRTermParser(termBuildingVisitor, termTypeChecker);
    }

    @Test
    public void fromStringNumber() throws TermParsingException {
        Term term = parser.fromString("1");
        Number expected = new Number(1);
        assertThat(term).isEqualTo(expected);
    }

    @Test
    public void fromStringConstant() throws TermParsingException {
        Term term = parser.fromString("c");
        Constant expected = new Constant("c");
        assertThat(term).isEqualTo(expected);
    }

    @Test
    public void fromStringPlus() throws TermParsingException {
        Term term = parser.fromString("1 + 2");
        Addition expected = new Addition(new Number(1), new Number(2));
        assertThat(term).isEqualTo(expected);
    }

    @Test
    public void fromStringMinus() throws TermParsingException {
        Term term = parser.fromString("1 - 2");
        Subtraction expected = new Subtraction(new Number(1), new Number(2));
        assertThat(term).isEqualTo(expected);
    }

    @Test
    public void fromStringMultiply() throws TermParsingException {
        Term term = parser.fromString("1 * 2");
        Multiplication expected = new Multiplication(new Number(1), new Number(2));
        assertThat(term).isEqualTo(expected);
    }

    @Test
    public void fromStringDivide() throws TermParsingException {
        Term term = parser.fromString("1 / 2");
        Division expected = new Division(new Number(1), new Number(2));
        assertThat(term).isEqualTo(expected);
    }

    @Test
    public void fromStringPower() throws TermParsingException {
        Term term = parser.fromString("1 ^ 2");
        Power expected = new Power(new Number(1), 2);
        assertThat(term).isEqualTo(expected);
    }

    @Test
    public void fromStringFunction() throws TermParsingException {
        Term term = parser.fromString("Foo(x, 1)");
        Function expected = new Function("Foo", Arrays.<Term>asList(new Constant("x"), new Number(1)));
        assertThat(term).isEqualTo(expected);
    }

    @Test
    public void fromNestedPlus() throws TermParsingException {
        Term term = parser.fromString("1 + 2 + 3");
        Addition expected = new Addition(new Addition(new Number(1), new Number(2)), new Number(3));
        assertThat(term).isEqualTo(expected);
    }

    @Test
    public void fromStringSummation() throws TermParsingException {
        Term term = parser.fromString("\\SUM i 0 10 i");
        Summation expected = new Summation(Variable.withTypeNat("i"), new Number(0), new Number(10),
                Variable.withTypeNat("i"));
        assertThat(term).isEqualTo(expected);
    }

    @Test(expected = TermParsingException.class)
    public void fromStringShouldThrowIfInvalidTermGiven() throws TermParsingException {
        parser.fromString("1 + 2 = 3");
    }

}

package com.ipandora.core.function;

import com.ipandora.api.predicate.formula.EqualToFormula;
import com.ipandora.api.predicate.function.*;
import com.ipandora.api.predicate.term.Addition;
import com.ipandora.api.predicate.term.Division;
import com.ipandora.api.predicate.term.Number;
import com.ipandora.api.predicate.term.Variable;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;

import static org.assertj.core.api.Assertions.assertThat;

public class ANTLRFunctionParserTest {

    @Test
    public void fromStringSingleCase() throws FunctionParsingException {
        ANTLRFunctionParser parser = new ANTLRFunctionParser();
        Function function = parser.fromString("Foo(x) = 1/x");

        FunctionCase functionCase = new FunctionCase(
                new Division(new Number(1), Variable.withTypeNat("x")),
                new OtherwiseCondition());

        MathematicalFunction expected = new MathematicalFunction(
                "Foo", Collections.singletonList(Variable.withTypeNat("x")), Collections.singletonList(functionCase));

        assertThat(function).isEqualTo(expected);
    }

    @Test
    public void fromStringManyCases() throws FunctionParsingException {
        ANTLRFunctionParser parser = new ANTLRFunctionParser();
        Function function = parser.fromString("Foo(x) = \n" +
                "1/2 if x = 1\n" +
                "1/3 otherwise");

        IfCondition ifCondition = new IfCondition(new EqualToFormula(Variable.withTypeNat("x"), new Number(1)));
        FunctionCase ifCase = new FunctionCase(new Division(new Number(1), new Number(2)), ifCondition);
        FunctionCase otherCase = new FunctionCase(new Division(new Number(1), new Number(3)), new OtherwiseCondition());

        MathematicalFunction expected = new MathematicalFunction(
                "Foo", Collections.singletonList(Variable.withTypeNat("x")), Arrays.asList(ifCase, otherCase));

        assertThat(function).isEqualTo(expected);
    }

    @Test
    public void fromStringManyArguments() throws FunctionParsingException {
        ANTLRFunctionParser parser = new ANTLRFunctionParser();
        Function function = parser.fromString("Foo(x, y) = x + y");

        FunctionCase functionCase = new FunctionCase(
                new Addition(Variable.withTypeNat("x"), Variable.withTypeNat("y")),
                new OtherwiseCondition());

        MathematicalFunction expected = new MathematicalFunction("Foo",
                Arrays.asList(Variable.withTypeNat("x"), Variable.withTypeNat("y")),
                Collections.singletonList(functionCase));

        assertThat(function).isEqualTo(expected);
    }

    @Test(expected = FunctionParsingException.class)
    public void fromStringShouldThrowIfNoArgumentsGiven() throws FunctionParsingException {
        ANTLRFunctionParser parser = new ANTLRFunctionParser();
        parser.fromString("Foo() = 1");
    }

}

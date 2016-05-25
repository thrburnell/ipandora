package com.ipandora.core.function;

import com.ipandora.api.predicate.formula.*;
import com.ipandora.api.predicate.function.FunctionCase;
import com.ipandora.api.predicate.function.FunctionDefinition;
import com.ipandora.api.predicate.function.FunctionPrototype;
import com.ipandora.api.predicate.function.MathematicalFunctionDefinition;
import com.ipandora.api.predicate.term.*;
import com.ipandora.api.predicate.term.Number;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.mockito.Mock;
import org.mockito.runners.MockitoJUnitRunner;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.core.api.Assertions.fail;
import static org.mockito.Matchers.any;
import static org.mockito.Matchers.anyList;
import static org.mockito.Mockito.doThrow;

@RunWith(MockitoJUnitRunner.class)
public class ANTLRFunctionParserTest {

    @Mock
    private FunctionTypeChecker mockTypeChecker;

    private ANTLRFunctionParser parser;

    @Before
    public void before() {
        parser = new ANTLRFunctionParser(mockTypeChecker);
    }

    @Test
    public void fromStringSingleCase() throws FunctionParsingException {
        FunctionDefinition function = parser.fromString("Foo(x) = 1/x");

        FunctionCase functionCase = new FunctionCase(
                new Division(new Number(1), Variable.withTypeNat("x")),
                new TruthFormula());

        MathematicalFunctionDefinition expected = new MathematicalFunctionDefinition(
                "Foo", Collections.singletonList(Variable.withTypeNat("x")), Collections.singletonList(functionCase));

        assertThat(function).isEqualTo(expected);
    }

    @Test
    public void fromStringTwoCases() throws FunctionParsingException {
        FunctionDefinition function = parser.fromString("Foo(x) = \n" +
                "1/2 if x = 1\n" +
                "1/3 otherwise");

        Formula ifCondition = new EqualToFormula(Variable.withTypeNat("x"), new Number(1));
        FunctionCase ifCase = new FunctionCase(new Division(new Number(1), new Number(2)), ifCondition);
        NotFormula otherCondition = new NotFormula(ifCondition);
        FunctionCase otherCase = new FunctionCase(new Division(new Number(1), new Number(3)), otherCondition);

        MathematicalFunctionDefinition expected = new MathematicalFunctionDefinition(
                "Foo", Collections.singletonList(Variable.withTypeNat("x")), Arrays.asList(ifCase, otherCase));

        assertThat(function).isEqualTo(expected);
    }

    @Test
    public void fromStringManyCases() throws FunctionParsingException {
        FunctionDefinition function = parser.fromString("Foo(x) = \n" +
                "1/2 if x = 1\n" +
                "1/3 if x = 2\n" +
                "1/8 otherwise");

        Formula ifCondition1 = new EqualToFormula(Variable.withTypeNat("x"), new Number(1));
        FunctionCase ifCase1 = new FunctionCase(new Division(new Number(1), new Number(2)), ifCondition1);

        Formula ifCondition2 = new EqualToFormula(Variable.withTypeNat("x"), new Number(2));
        FunctionCase ifCase2 = new FunctionCase(new Division(new Number(1), new Number(3)), ifCondition2);

        AndFormula otherCondition = new AndFormula(new NotFormula(ifCondition1), new NotFormula(ifCondition2));
        FunctionCase otherCase = new FunctionCase(new Division(new Number(1), new Number(8)), otherCondition);

        MathematicalFunctionDefinition expected = new MathematicalFunctionDefinition("Foo",
                Collections.singletonList(Variable.withTypeNat("x")), Arrays.asList(ifCase1, ifCase2, otherCase));

        assertThat(function).isEqualTo(expected);
    }

    @Test
    public void fromStringManyArguments() throws FunctionParsingException {
        FunctionDefinition function = parser.fromString("Foo(x, y) = x + y");

        FunctionCase functionCase = new FunctionCase(
                new Addition(Variable.withTypeNat("x"), Variable.withTypeNat("y")),
                new TruthFormula());

        MathematicalFunctionDefinition expected = new MathematicalFunctionDefinition("Foo",
                Arrays.asList(Variable.withTypeNat("x"), Variable.withTypeNat("y")),
                Collections.singletonList(functionCase));

        assertThat(function).isEqualTo(expected);
    }

    @Test(expected = FunctionParsingException.class)
    public void fromStringShouldThrowIfNoArgumentsGiven() throws FunctionParsingException {
        parser.fromString("Foo() = 1");
    }

    @Test(expected = TypeMismatchException.class)
    public void fromStringWithTypeCheckingShouldThrowWithCauseIfTypeCheckerThrows() throws Throwable {

        doThrow(new TypeMismatchException("test")).
                when(mockTypeChecker).analyse(any(FunctionDefinition.class), anyList());

        try {
            parser.fromStringWithTypeChecking("Foo(x) = \n" +
                    "1/2 if c = 1\n" +
                    "1/3 otherwise");

            fail("FunctionParsingException should have been thrown!");
        } catch (FunctionParsingException e) {
            throw e.getCause();
        }
    }

    @Test
    public void fromStringWithFunctionPrototypesShouldReturnTypedExpression() throws FunctionParsingException {
        List<FunctionPrototype> functionPrototypes = new ArrayList<>();
        functionPrototypes.add(new FunctionPrototype("Bar", Collections.singletonList(Type.NAT), Type.NAT));

        FunctionDefinition function = parser.fromString("Foo(x) = \n" +
                "1/2 if Bar(x) = 1\n" +
                "1/3 otherwise", functionPrototypes);

        Formula ifCondition = new EqualToFormula(new Function("Bar",
                Collections.<Term>singletonList(Variable.withTypeNat("x")), Type.NAT), new Number(1));
        FunctionCase ifCase = new FunctionCase(new Division(new Number(1), new Number(2)), ifCondition);
        NotFormula otherCondition = new NotFormula(ifCondition);
        FunctionCase otherCase = new FunctionCase(new Division(new Number(1), new Number(3)), otherCondition);

        MathematicalFunctionDefinition expected = new MathematicalFunctionDefinition(
                "Foo", Collections.singletonList(Variable.withTypeNat("x")), Arrays.asList(ifCase, otherCase));

        assertThat(function).isEqualTo(expected);
    }

}

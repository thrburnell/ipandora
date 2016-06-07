package com.ipandora.core.function;

import com.ipandora.api.predicate.function.FunctionCase;
import com.ipandora.api.predicate.function.FunctionPrototype;
import com.ipandora.api.predicate.function.MathematicalFunctionDefinition;
import com.ipandora.api.predicate.term.Type;
import com.ipandora.api.predicate.term.Variable;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;

import static org.assertj.core.api.Assertions.assertThat;

public class FunctionPrototypeBuildingVisitorTest {

    @Test
    public void visitMathematicalFunctionDefinitionShouldReturnCorrectPrototype() {
        MathematicalFunctionDefinition fn = new MathematicalFunctionDefinition("Foo",
                Arrays.asList(Variable.withTypeNat("x"), new Variable("y")), Collections.<FunctionCase>emptyList(),
                Type.NAT);

        FunctionPrototype expected = new FunctionPrototype("Foo", Arrays.asList(Type.NAT, Type.UNKNOWN), Type.NAT);
        FunctionPrototypeBuildingVisitor visitor = new FunctionPrototypeBuildingVisitor();
        FunctionPrototype prototype = visitor.visit(fn);
        assertThat(prototype).isEqualTo(expected);
    }

}

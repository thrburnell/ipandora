package com.ipandora.core.term;

import com.ipandora.api.predicate.term.Constant;
import com.ipandora.api.predicate.term.Function;
import com.ipandora.api.predicate.term.Subtraction;
import com.ipandora.api.predicate.term.Variable;
import org.junit.Test;

import java.util.List;

import static com.ipandora.testutils.TermCreators.*;
import static org.assertj.core.api.Assertions.assertThat;

public class AtomCollectingTermVisitorTest {

    // 1 + Foo(x + y, a/2) / Bar(b + 5) - z^3
    private static final Function foo = fun("Foo", add(natVar("x"), natVar("y")), div(con("a"), num(2)));
    private static final Function bar = fun("Bar", add(con("b"), num(5)));
    private static final Subtraction term = sub(add(num(1), div(foo, bar)), pow(natVar("z"), 3));

    @Test
    public void getVariablesShouldReturnAllVariablesAfterVisit() {
        AtomCollectingTermVisitor visitor = new AtomCollectingTermVisitor();
        visitor.visit(term);
        List<Variable> variables = visitor.getVariables();
        assertThat(variables).containsExactlyInAnyOrder(natVar("x"), natVar("y"), natVar("z"));
    }

    @Test
    public void getConstantsShouldReturnAllConstantsAfterVisit() {
        AtomCollectingTermVisitor visitor = new AtomCollectingTermVisitor();
        visitor.visit(term);
        List<Constant> constants = visitor.getConstants();
        assertThat(constants).containsExactlyInAnyOrder(con("a"), con("b"));
    }

    @Test
    public void getFunctionsShouldReturnAllFunctionsAfterVisit() {
        AtomCollectingTermVisitor visitor = new AtomCollectingTermVisitor();
        visitor.visit(term);
        List<Function> functions = visitor.getFunctions();
        assertThat(functions).containsExactlyInAnyOrder(foo, bar);
    }

}

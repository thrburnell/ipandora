package com.ipandora.core.z3;

import com.ipandora.api.predicate.term.Constant;
import com.ipandora.api.predicate.term.Variable;
import org.junit.Test;

import java.util.Set;

import static org.assertj.core.api.Assertions.assertThat;

public class SMTGeneratingTermVisitorTest {

    @Test
    public void visitVariableReturnsNameOfVariable() {
        SMTGeneratingTermVisitor visitor = new SMTGeneratingTermVisitor();
        String result = visitor.visitVariable(new Variable("x"));
        assertThat(result).isEqualTo("x");
    }

    @Test
    public void visitConstantReturnsNameOfConstant() {
        SMTGeneratingTermVisitor visitor = new SMTGeneratingTermVisitor();
        String result = visitor.visitConstant(new Constant("y"));
        assertThat(result).isEqualTo("y");
    }

    @Test
    public void getConstantsReturnsEmptySetIfNoConstantsVisited() {

        SMTGeneratingTermVisitor visitor = new SMTGeneratingTermVisitor();
        visitor.visit(new Variable("x"));
        visitor.visit(new Variable("y"));
        visitor.visit(new Variable("x"));

        Set<String> constants = visitor.getConstants();
        assertThat(constants).isEmpty();
    }

    @Test
    public void getConstantsReturnsSetWithNamesOfAllConstantsVisited() {
        SMTGeneratingTermVisitor visitor = new SMTGeneratingTermVisitor();
        visitor.visit(new Variable("x"));
        visitor.visit(new Constant("x"));
        visitor.visit(new Constant("y"));
        visitor.visit(new Variable("z"));
        visitor.visit(new Constant("y"));

        Set<String> constants = visitor.getConstants();
        assertThat(constants).hasSize(2).contains("x").contains("y");
    }

}

package com.ipandora.core.z3;

import com.ipandora.api.predicate.term.*;
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

    @Test
    public void visitAdditionReturnsCorrectCode() {
        SMTGeneratingTermVisitor visitor = new SMTGeneratingTermVisitor();
        String result = visitor.visit(new Addition(new Variable("x"), new Constant("y")));
        assertThat(result).isEqualTo("(+ x y)");
    }

    @Test
    public void visitSubtractionReturnsCorrectCode() {
        SMTGeneratingTermVisitor visitor = new SMTGeneratingTermVisitor();
        String result = visitor.visit(new Subtraction(new Variable("x"), new Constant("y")));
        assertThat(result).isEqualTo("(- x y)");
    }

    @Test
    public void visitMultiplicationReturnsCorrectCode() {
        SMTGeneratingTermVisitor visitor = new SMTGeneratingTermVisitor();
        String result = visitor.visit(new Multiplication(new Variable("x"), new Constant("y")));
        assertThat(result).isEqualTo("(* x y)");
    }

    @Test
    public void visitDivisionReturnsCorrectCode() {
        SMTGeneratingTermVisitor visitor = new SMTGeneratingTermVisitor();
        String result = visitor.visit(new Division(new Variable("x"), new Constant("y")));
        assertThat(result).isEqualTo("(/ x y)");
    }

    @Test
    public void visitAdditionReturnsCorrectCodeForNestedTerms() {
        SMTGeneratingTermVisitor visitor = new SMTGeneratingTermVisitor();
        Addition addition = new Addition(new Addition(new Variable("x"), new Variable("y")), new Constant("z"));
        String result = visitor.visit(addition);
        assertThat(result).isEqualTo("(+ (+ x y) z)");
    }

    @Test
    public void visitSubtractionReturnsCorrectCodeForNestedTerms() {
        SMTGeneratingTermVisitor visitor = new SMTGeneratingTermVisitor();
        Subtraction addition = new Subtraction(new Variable("x"),
                new Subtraction(new Variable("y"), new Constant("z")));

        String result = visitor.visit(addition);
        assertThat(result).isEqualTo("(- x (- y z))");
    }

    @Test
    public void visitMultiplicationReturnsCorrectCodeForNestedTerms() {
        SMTGeneratingTermVisitor visitor = new SMTGeneratingTermVisitor();
        Multiplication addition = new Multiplication(
                new Multiplication(new Variable("x"), new Variable("y")),
                new Multiplication(new Variable("m"), new Variable("n")));

        String result = visitor.visit(addition);
        assertThat(result).isEqualTo("(* (* x y) (* m n))");
    }

    @Test
    public void visitDivisionReturnsCorrectCodeForNestedTerms() {
        SMTGeneratingTermVisitor visitor = new SMTGeneratingTermVisitor();
        Division addition = new Division(new Division(new Variable("x"), new Variable("y")), new Constant("z"));
        String result = visitor.visit(addition);
        assertThat(result).isEqualTo("(/ (/ x y) z)");
    }

}

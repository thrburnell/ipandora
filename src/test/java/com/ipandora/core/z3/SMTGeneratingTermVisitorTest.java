package com.ipandora.core.z3;

import com.ipandora.api.predicate.term.*;
import com.ipandora.api.predicate.term.Number;
import org.junit.Test;

import java.util.Arrays;
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
        String result = visitor.visit(new Addition(Variable.withTypeNat("x"), Variable.withTypeNat("y")));
        assertThat(result).isEqualTo("(+ x y)");
    }

    @Test
    public void visitSubtractionReturnsCorrectCode() {
        SMTGeneratingTermVisitor visitor = new SMTGeneratingTermVisitor();
        String result = visitor.visit(new Subtraction(Variable.withTypeNat("x"), Variable.withTypeNat("y")));
        assertThat(result).isEqualTo("(- x y)");
    }

    @Test
    public void visitMultiplicationReturnsCorrectCode() {
        SMTGeneratingTermVisitor visitor = new SMTGeneratingTermVisitor();
        String result = visitor.visit(new Multiplication(Variable.withTypeNat("x"), Variable.withTypeNat("y")));
        assertThat(result).isEqualTo("(* x y)");
    }

    @Test
    public void visitDivisionReturnsCorrectCode() {
        SMTGeneratingTermVisitor visitor = new SMTGeneratingTermVisitor();
        String result = visitor.visit(new Division(Variable.withTypeNat("x"), Variable.withTypeNat("y")));
        assertThat(result).isEqualTo("(/ x y)");
    }

    @Test
    public void visitAdditionReturnsCorrectCodeForNestedTerms() {
        SMTGeneratingTermVisitor visitor = new SMTGeneratingTermVisitor();
        Addition addition = new Addition(new Addition(Variable.withTypeNat("x"), Variable.withTypeNat("y")),
                Variable.withTypeNat("z"));
        String result = visitor.visit(addition);
        assertThat(result).isEqualTo("(+ (+ x y) z)");
    }

    @Test
    public void visitSubtractionReturnsCorrectCodeForNestedTerms() {
        SMTGeneratingTermVisitor visitor = new SMTGeneratingTermVisitor();
        Subtraction addition = new Subtraction(Variable.withTypeNat("x"),
                new Subtraction(Variable.withTypeNat("y"), Variable.withTypeNat("z")));

        String result = visitor.visit(addition);
        assertThat(result).isEqualTo("(- x (- y z))");
    }

    @Test
    public void visitMultiplicationReturnsCorrectCodeForNestedTerms() {
        SMTGeneratingTermVisitor visitor = new SMTGeneratingTermVisitor();
        Multiplication addition = new Multiplication(
                new Multiplication(Variable.withTypeNat("x"), Variable.withTypeNat("y")),
                new Multiplication(Variable.withTypeNat("m"), Variable.withTypeNat("n")));

        String result = visitor.visit(addition);
        assertThat(result).isEqualTo("(* (* x y) (* m n))");
    }

    @Test
    public void visitDivisionReturnsCorrectCodeForNestedTerms() {
        SMTGeneratingTermVisitor visitor = new SMTGeneratingTermVisitor();
        Division addition = new Division(new Division(Variable.withTypeNat("x"), Variable.withTypeNat("y")),
                Variable.withTypeNat("z"));
        String result = visitor.visit(addition);
        assertThat(result).isEqualTo("(/ (/ x y) z)");
    }

    @Test
    public void visitNumberReturnsNumber() {
        SMTGeneratingTermVisitor visitor = new SMTGeneratingTermVisitor();
        String result = visitor.visit(new Number(13));
        assertThat(result).isEqualTo("13");
    }

    @Test
    public void visitFunctionReturnsCorrectCode() {
        SMTGeneratingTermVisitor visitor = new SMTGeneratingTermVisitor();
        Function function = new Function("f", Arrays.asList(new Variable("x"), new Constant("y")));
        String result = visitor.visit(function);
        assertThat(result).isEqualTo("(f x y)");
    }

    @Test
    public void visitFunctionReturnsCorrectCodeForNestedFunctions() {
        SMTGeneratingTermVisitor visitor = new SMTGeneratingTermVisitor();
        Function f = new Function("f", Arrays.<Term>asList(new Variable("x"), new Variable("y")));
        Function g = new Function("g", Arrays.asList(new Variable("x"), f));
        String result = visitor.visit(g);
        assertThat(result).isEqualTo("(g x (f x y))");
    }

    @Test
    public void visitPowerReturnsCorrectCode() {
        SMTGeneratingTermVisitor visitor = new SMTGeneratingTermVisitor();
        Power power = new Power(Variable.withTypeNat("x"), 3);
        String result = visitor.visit(power);
        assertThat(result).isEqualTo("(^ x 3)");
    }

    @Test
    public void visitPowerReturnsCorrectCodeForNestedPowers() {
        SMTGeneratingTermVisitor visitor = new SMTGeneratingTermVisitor();
        Power power = new Power(new Power(Variable.withTypeNat("x"), 2), 3);
        String result = visitor.visit(power);
        assertThat(result).isEqualTo("(^ (^ x 2) 3)");
    }

}

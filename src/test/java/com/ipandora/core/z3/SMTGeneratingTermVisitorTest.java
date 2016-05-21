package com.ipandora.core.z3;

import com.ipandora.api.predicate.term.FunctionPrototype;
import com.ipandora.api.predicate.term.*;
import com.ipandora.api.predicate.term.Number;
import com.ipandora.core.util.WrappingRuntimeException;
import org.junit.Test;

import java.util.Arrays;
import java.util.List;
import java.util.Map;

import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.core.api.Assertions.fail;

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

    @Test(expected = TypeMismatchException.class)
    public void visitConstantThrowsIfConstantUsedMultipleTimesWithDifferentType() throws Exception {
        SMTGeneratingTermVisitor visitor = new SMTGeneratingTermVisitor();
        visitor.visit(new Constant("x"));

        try {
            visitor.visit(new Constant("x", Type.NAT));
            fail("WrappingRuntimeException should have been thrown!");
        } catch (WrappingRuntimeException wre) {
            throw wre.getWrappedException();
        }
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
        Function function = new Function("f", Arrays.<Term>asList(new Variable("x"), new Constant("y")));
        String result = visitor.visit(function);
        assertThat(result).isEqualTo("(f x y)");
    }

    @Test
    public void visitFunctionReturnsCorrectCodeForNestedFunctions() {
        SMTGeneratingTermVisitor visitor = new SMTGeneratingTermVisitor();
        Function f = new Function("f", Arrays.<Term>asList(new Variable("x"), new Variable("y")));
        Function g = new Function("g", Arrays.<Term>asList(new Variable("x"), f));
        String result = visitor.visit(g);
        assertThat(result).isEqualTo("(g x (f x y))");
    }

    @Test(expected = TypeMismatchException.class)
    public void visitFunctionThrowsIfFunctionUsedMultipleTimesWithDifferentReturnType() throws Exception {
        SMTGeneratingTermVisitor visitor = new SMTGeneratingTermVisitor();
        visitor.visit(new Function("Foo", Arrays.<Term>asList(new Variable("x"), Variable.withTypeNat("y")), Type.NAT));

        try {
            visitor.visit(new Function("Foo", Arrays.<Term>asList(new Variable("x"), Variable.withTypeNat("y")), Type.UNKNOWN));
            fail("WrappingRuntimeException should have been thrown!");
        } catch (WrappingRuntimeException wre) {
            throw wre.getWrappedException();
        }
    }

    @Test(expected = TypeMismatchException.class)
    public void visitFunctionThrowsIfFunctionUsedMultipleTimesWithDifferentArgTypes() throws Exception {
        SMTGeneratingTermVisitor visitor = new SMTGeneratingTermVisitor();
        visitor.visit(new Function("Foo", Arrays.<Term>asList(new Variable("x"), Variable.withTypeNat("y")), Type.NAT));

        try {
            visitor.visit(new Function("Foo", Arrays.<Term>asList(Variable.withTypeNat("x"), Variable.withTypeNat("y")), Type.NAT));
            fail("WrappingRuntimeException should have been thrown!");
        } catch (WrappingRuntimeException wre) {
            throw wre.getWrappedException();
        }
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

    @Test
    public void getConstantNamesToTypesReturnsEmptySetIfNoConstantsVisited() {

        SMTGeneratingTermVisitor visitor = new SMTGeneratingTermVisitor();
        visitor.visit(new Variable("x"));
        visitor.visit(new Variable("y"));
        visitor.visit(new Variable("x"));

        Map<String, Type> constantNamesToTypes = visitor.getConstantNamesToTypes();
        assertThat(constantNamesToTypes).isEmpty();
    }

    @Test
    public void getConstantNamesToTypesReturnsCorrectMap() {
        SMTGeneratingTermVisitor visitor = new SMTGeneratingTermVisitor();
        Constant x = new Constant("x");
        Constant y = new Constant("y", Type.NAT);

        visitor.visit(new Variable("x"));
        visitor.visit(x);
        visitor.visit(y);
        visitor.visit(new Variable("z"));
        visitor.visit(y);

        Map<String, Type> constantNamesToTypes = visitor.getConstantNamesToTypes();
        assertThat(constantNamesToTypes).hasSize(2).containsEntry("x", Type.UNKNOWN).containsEntry("y", Type.NAT);
    }

    @Test
    public void getFunctionPrototypesReturnsCorrectList() {

        SMTGeneratingTermVisitor visitor = new SMTGeneratingTermVisitor();

        // Foo (Int, Type) Type
        Function foo = new Function("Foo", Arrays.asList(new Addition(new Number(2), new Number(3)),
                new Constant("C")));

        // Bar (Type, Int, Int) Int
        Function bar = new Function("Bar", Arrays.asList(new Variable("x"), Variable.withTypeNat("y"),
                new Power(new Number(1), 1)), Type.NAT);

        visitor.visit(foo);
        visitor.visit(bar);

        List<FunctionPrototype> functionPrototypes = visitor.getFunctionPrototypes();
        assertThat(functionPrototypes).hasSize(2)
                .contains(new FunctionPrototype("Foo", Arrays.asList(Type.NAT, Type.UNKNOWN), Type.UNKNOWN))
                .contains(new FunctionPrototype("Bar", Arrays.asList(Type.UNKNOWN, Type.NAT, Type.NAT), Type.NAT));
    }

}

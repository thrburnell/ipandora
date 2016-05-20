package com.ipandora.core.term;

import com.ipandora.api.predicate.term.*;
import com.ipandora.api.predicate.term.Number;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class AtomCollectingTermVisitor implements TermVisitor<Void> {

    private final List<Constant> constants = new ArrayList<>();
    private final List<Variable> variables = new ArrayList<>();
    private final List<Function> functions = new ArrayList<>();

    public List<Constant> getConstants() {
        return constants;
    }

    public Set<Constant> getUniqueConstants() {
        return new HashSet<>(getConstants());
    }

    public List<Variable> getVariables() {
        return variables;
    }

    public Set<Variable> getUniqueVariables() {
        return new HashSet<>(getVariables());
    }

    public List<Function> getFunctions() {
        return functions;
    }

    @Override
    public Void visit(Term term) {
        return term.accept(this);
    }

    @Override
    public Void visitConstant(Constant constant) {
        constants.add(constant);
        return null;
    }

    @Override
    public Void visitVariable(Variable variable) {
        variables.add(variable);
        return null;
    }

    @Override
    public Void visitAddition(Addition addition) {
        return visitArithmeticExpression(addition);
    }

    @Override
    public Void visitSubtraction(Subtraction subtraction) {
        return visitArithmeticExpression(subtraction);
    }

    @Override
    public Void visitMultiplication(Multiplication multiplication) {
        return visitArithmeticExpression(multiplication);
    }

    @Override
    public Void visitDivision(Division division) {
        return visitArithmeticExpression(division);
    }

    private Void visitArithmeticExpression(ArithmeticExpression arithmeticExpression) {
        visit(arithmeticExpression.getLeft());
        visit(arithmeticExpression.getRight());
        return null;
    }

    @Override
    public Void visitNumber(Number number) {
        return null;
    }

    @Override
    public Void visitFunction(Function function) {
        for (Term arg : function.getArgs()) {
            visit(arg);
        }
        functions.add(function);
        return null;
    }

    @Override
    public Void visitPower(Power power) {
        visit(power.getBase());
        return null;
    }

    @Override
    public Void visitSummation(Summation summation) {
        visit(summation.getVariable());
        visit(summation.getLowerBound());
        visit(summation.getUpperBound());
        visit(summation.getElement());
        return null;
    }

}

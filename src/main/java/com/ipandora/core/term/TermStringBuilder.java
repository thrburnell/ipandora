package com.ipandora.core.term;

import com.ipandora.api.predicate.term.*;
import com.ipandora.api.predicate.term.Number;
import com.ipandora.core.util.PrettyStringBuilder;
import org.apache.commons.lang3.StringUtils;

import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

public class TermStringBuilder implements PrettyStringBuilder<Term>, TermVisitor<String> {

    private final Stack<ArithmeticOperator> operatorStack = new Stack<>();

    @Override
    public String build(Term term) {
        return visit(term);
    }

    @Override
    public String visit(Term term) {
        return term.accept(this);
    }

    @Override
    public String visitConstant(Constant constant) {
        return constant.getName();
    }

    @Override
    public String visitVariable(Variable variable) {
        return variable.getName();
    }

    @Override
    public String visitAddition(Addition addition) {
        ArithmeticOperator plus = ArithmeticOperator.PLUS;
        operatorStack.push(plus);
        String left = visit(addition.getLeft());
        String right = visit(addition.getRight());
        operatorStack.pop();

        String result = String.format("%s + %s", left, right);

        if (doesCurrentContextBindStronger(plus)) {
            result = wrapInParenthesis(result);
        }

        return result;
    }

    @Override
    public String visitSubtraction(Subtraction subtraction) {
        ArithmeticOperator minus = ArithmeticOperator.MINUS;
        operatorStack.push(minus);
        String left = visit(subtraction.getLeft());
        operatorStack.push(ArithmeticOperator.MINUS_RIGHT);
        String right = visit(subtraction.getRight());
        operatorStack.pop();
        operatorStack.pop();

        String result = String.format("%s - %s", left, right);

        if (doesCurrentContextBindStronger(minus)) {
            result = wrapInParenthesis(result);
        }

        return result;
    }

    @Override
    public String visitMultiplication(Multiplication multiplication) {
        ArithmeticOperator multiply = ArithmeticOperator.MULTIPLY;
        operatorStack.push(multiply);
        String left = visit(multiplication.getLeft());
        String right = visit(multiplication.getRight());
        operatorStack.pop();

        String result = String.format("%s * %s", left, right);

        if (doesCurrentContextBindStrongerOrEqual(multiply)) {
            result = wrapInParenthesis(result);
        }

        return result;
    }

    @Override
    public String visitDivision(Division division) {
        ArithmeticOperator divide = ArithmeticOperator.DIVIDE;
        operatorStack.push(divide);
        String left = visit(division.getLeft());
        String right = visit(division.getRight());
        operatorStack.pop();

        String result = String.format("%s / %s", left, right);

        if (doesCurrentContextBindStrongerOrEqual(divide)) {
            result = wrapInParenthesis(result);
        }

        return result;
    }

    @Override
    public String visitNumber(Number number) {
        return String.valueOf(number.getNumber());
    }

    @Override
    public String visitFunction(Function function) {

        String name = function.getName();

        List<String> argStrings = new ArrayList<>();
        for (Term arg : function.getArgs()) {
            argStrings.add(visit(arg));
        }

        String argString = StringUtils.join(argStrings, ", ");
        return String.format("%s(%s)", name, argString);
    }

    @Override
    public String visitPower(Power power) {

        ArithmeticOperator pow = ArithmeticOperator.POWER;
        operatorStack.push(pow);
        String base = visit(power.getBase());
        operatorStack.pop();

        String result = String.format("%s^%d", base, power.getExponent());

        if (doesCurrentContextBindStronger(pow)) {
            result = wrapInParenthesis(result);
        }

        return result;
    }

    @Override
    public String visitSummation(Summation summation) {
        ArithmeticOperator sum = ArithmeticOperator.SUM;
        operatorStack.push(sum);
        String variable = visit(summation.getVariable());
        String lowerBound = visit(summation.getLowerBound());
        String upperBound = visit(summation.getUpperBound());
        String element = visit(summation.getElement());
        operatorStack.pop();

        String result = String.format("\\SUM %s %s %s %s", variable, lowerBound, upperBound, element);

        if (doesCurrentContextBindStronger(sum)) {
            result = wrapInParenthesis(result);
        }

        return result;
    }

    private boolean doesCurrentContextBindStronger(ArithmeticOperator operator) {
        return !operatorStack.isEmpty() && operatorStack.peek().getPrecedence() > operator.getPrecedence();
    }

    private boolean doesCurrentContextBindStrongerOrEqual(ArithmeticOperator operator) {
        return !operatorStack.isEmpty() && operatorStack.peek().getPrecedence() >= operator.getPrecedence();
    }

    private String wrapInParenthesis(String result) {
        return String.format("(%s)", result);
    }

}

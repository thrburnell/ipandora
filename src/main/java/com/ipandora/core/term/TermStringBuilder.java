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
        ArithmeticOperator minusRight = ArithmeticOperator.MINUS_RIGHT;

        operatorStack.push(minus);
        String left = visit(subtraction.getLeft());
        operatorStack.push(minusRight);
        String right = visit(subtraction.getRight());
        operatorStack.pop();
        operatorStack.pop();

        String result = String.format("%s - %s", left, right);

        if (doesCurrentContextBindStronger(minus) && isCurrentContextDifferentTo(minusRight)) {
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

        if (doesCurrentContextBindStrongerOrEqual(multiply) && isCurrentContextDifferentTo(multiply)) {
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

    private boolean doesCurrentContextBindStronger(ArithmeticOperator operator) {
        return !operatorStack.isEmpty() && operatorStack.peek().getPrecedence() > operator.getPrecedence();
    }

    private boolean doesCurrentContextBindStrongerOrEqual(ArithmeticOperator operator) {
        return !operatorStack.isEmpty() && operatorStack.peek().getPrecedence() >= operator.getPrecedence();
    }

    private boolean isCurrentContextDifferentTo(ArithmeticOperator operator) {
        return !operatorStack.isEmpty() && operatorStack.peek() != operator;
    }

    private String wrapInParenthesis(String result) {
        return String.format("(%s)", result);
    }

}

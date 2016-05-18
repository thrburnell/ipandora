package com.ipandora.core.term;

public enum ArithmeticOperator {

    POWER(5),
    DIVIDE(4),
    MULTIPLY(4),
    SUM(3),
    MINUS_RIGHT(2),
    MINUS(1),
    PLUS(1);

    private int precedence;

    ArithmeticOperator(int precedence) {
        this.precedence = precedence;
    }

    public int getPrecedence() {
        return precedence;
    }

}

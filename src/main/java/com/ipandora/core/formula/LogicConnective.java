package com.ipandora.core.formula;

public enum LogicConnective {

    FORALL(5),
    EXISTS(5),
    NOT(5),
    AND(4),
    OR(3),
    IMPLIES(2),
    IFF(1);

    private int precedence;

    LogicConnective(int precedence) {
        this.precedence = precedence;
    }

    public int getPrecedence() {
        return precedence;
    }
}

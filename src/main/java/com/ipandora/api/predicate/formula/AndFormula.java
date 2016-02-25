package com.ipandora.api.predicate.formula;

public class AndFormula implements Formula {

    private Formula left;
    private Formula right;

    public AndFormula(Formula left, Formula right) {
        this.left = left;
        this.right = right;
    }

    @Override
    public String toString() {
        return String.format("(%s) \u2227 (%s)", left, right);
    }

}

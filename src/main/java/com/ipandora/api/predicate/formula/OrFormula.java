package com.ipandora.api.predicate.formula;

public class OrFormula implements Formula {

    private final Formula left;
    private final Formula right;

    public OrFormula(Formula left, Formula right) {
        this.left = left;
        this.right = right;
    }

    @Override
    public String toString() {
        return String.format("(%s) \u2228 (%s)", left, right);
    }

}

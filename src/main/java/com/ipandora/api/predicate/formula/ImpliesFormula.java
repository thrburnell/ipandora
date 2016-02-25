package com.ipandora.api.predicate.formula;

public class ImpliesFormula implements Formula {

    private final Formula left;
    private final Formula right;

    public ImpliesFormula(Formula left, Formula right) {
        this.left = left;
        this.right = right;
    }

    @Override
    public String toString() {
        return String.format("(%s) \u2192 (%s)", left, right);
    }

}

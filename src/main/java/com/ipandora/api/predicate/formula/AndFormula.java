package com.ipandora.api.predicate.formula;

import com.ipandora.core.formula.FormulaVisitor;

public class AndFormula implements Formula {

    private Formula left;
    private Formula right;

    public AndFormula(Formula left, Formula right) {
        this.left = left;
        this.right = right;
    }

    public Formula getLeft() {
        return left;
    }

    public Formula getRight() {
        return right;
    }

    @Override
    public String toString() {
        return String.format("(%s) \u2227 (%s)", left, right);
    }

    @Override
    public <T> T accept(FormulaVisitor<T> visitor) {
        return visitor.visitAndFormula(this);
    }
}

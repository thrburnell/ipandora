package com.ipandora.api.predicate.formula;

import com.ipandora.core.formula.FormulaVisitor;

public class ImpliesFormula implements Formula {

    private final Formula left;
    private final Formula right;

    public ImpliesFormula(Formula left, Formula right) {
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
        return String.format("(%s) \u2192 (%s)", left, right);
    }

    @Override
    public <T> T accept(FormulaVisitor<T> visitor) {
        return visitor.visitImpliesFormula(this);
    }

}

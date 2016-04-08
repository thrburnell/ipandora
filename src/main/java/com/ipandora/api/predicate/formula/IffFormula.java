package com.ipandora.api.predicate.formula;

import com.ipandora.core.formula.FormulaVisitor;

public class IffFormula implements Formula {

    private final Formula left;
    private final Formula right;

    public IffFormula(Formula left, Formula right) {
        this.left = left;
        this.right = right;
    }

    @Override
    public String toString() {
        return String.format("(%s) \u2194 (%s)", left, right);
    }

    @Override
    public <T> T accept(FormulaVisitor<T> visitor) {
        return visitor.visitIffFormula(this);
    }

}

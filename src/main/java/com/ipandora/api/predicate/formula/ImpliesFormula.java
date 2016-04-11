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

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        ImpliesFormula that = (ImpliesFormula) o;

        if (left != null ? !left.equals(that.left) : that.left != null) return false;
        return !(right != null ? !right.equals(that.right) : that.right != null);

    }

    @Override
    public int hashCode() {
        int result = left != null ? left.hashCode() : 0;
        result = 31 * result + (right != null ? right.hashCode() : 0);
        return result;
    }
}

package com.ipandora.api.predicate.formula;

import com.ipandora.core.formula.FormulaVisitor;

public class OrFormula implements Formula {

    private final Formula left;
    private final Formula right;

    public OrFormula(Formula left, Formula right) {
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
        return String.format("(%s) \u2228 (%s)", left, right);
    }

    @Override
    public <T> T accept(FormulaVisitor<T> visitor) {
        return visitor.visitOrFormula(this);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        OrFormula orFormula = (OrFormula) o;

        if (left != null ? !left.equals(orFormula.left) : orFormula.left != null) return false;
        return !(right != null ? !right.equals(orFormula.right) : orFormula.right != null);

    }

    @Override
    public int hashCode() {
        int result = left != null ? left.hashCode() : 0;
        result = 31 * result + (right != null ? right.hashCode() : 0);
        return result;
    }
}

package com.ipandora.api.predicate.formula;

import com.ipandora.api.predicate.term.Term;
import com.ipandora.core.formula.FormulaVisitor;

public class GreaterThanFormula implements Formula {

    private final Term left;
    private final Term right;

    public GreaterThanFormula(Term left, Term right) {
        this.left = left;
        this.right = right;
    }

    public Term getLeft() {
        return left;
    }

    public Term getRight() {
        return right;
    }

    @Override
    public <T> T accept(FormulaVisitor<T> visitor) {
        return visitor.visitGreaterThanFormula(this);
    }

    @Override
    public String toString() {
        return String.format("%s > %s", left, right);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        GreaterThanFormula that = (GreaterThanFormula) o;

        if (!left.equals(that.left)) return false;
        return right.equals(that.right);
    }

    @Override
    public int hashCode() {
        int result = left.hashCode();
        result = 31 * result + right.hashCode();
        return result;
    }

}

package com.ipandora.api.predicate.term;

import com.ipandora.core.term.TermVisitor;

public class Subtraction implements ArithmeticExpression {

    private final Term left;
    private final Term right;

    public Subtraction(Term left, Term right) {
        this.left = left;
        this.right = right;
    }

    @Override
    public Term getLeft() {
        return left;
    }

    @Override
    public Term getRight() {
        return right;
    }

    @Override
    public <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitSubtraction(this);
    }

    @Override
    public String toString() {
        return String.format("(%s - %s)", left, right);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        Subtraction that = (Subtraction) o;

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

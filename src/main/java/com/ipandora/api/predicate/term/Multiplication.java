package com.ipandora.api.predicate.term;

import com.ipandora.core.term.TermVisitor;

public class Multiplication extends ArithmeticExpression {

    public Multiplication(Term left, Term right) {
        super(left, right);
    }

    @Override
    public <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitMultiplication(this);
    }

    @Override
    public String toString() {
        return String.format("(%s * %s)", left, right);
    }

}

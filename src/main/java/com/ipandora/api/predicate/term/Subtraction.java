package com.ipandora.api.predicate.term;

import com.ipandora.core.term.TermVisitor;

public class Subtraction extends ArithmeticExpression {

    public Subtraction(Term left, Term right) {
        super(left, right);
    }

    @Override
    public <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitSubtraction(this);
    }

    @Override
    public String toString() {
        return String.format("(%s - %s)", left, right);
    }

}

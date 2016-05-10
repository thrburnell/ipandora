package com.ipandora.api.predicate.term;

import com.ipandora.core.term.TermVisitor;

public class Addition extends ArithmeticExpression {

    public Addition(Term left, Term right) {
        super(left, right);
    }

    @Override
    public <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitAddition(this);
    }

    @Override
    public String toString() {
        return String.format("(%s + %s)", left, right);
    }

}

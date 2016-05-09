package com.ipandora.api.predicate.term;

public interface ArithmeticExpression extends Term {

    Term getLeft();
    Term getRight();

}

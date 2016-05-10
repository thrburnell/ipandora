package com.ipandora.api.predicate.term;

import org.junit.Test;

public class SummationTest {

    @Test(expected = TypeMismatchException.class)
    public void constructionShouldThrowIfVariableHasUnknownType() {
        new Summation(new Variable("x", Type.UNKNOWN), new Number(0), new Variable("n", Type.NAT), new Number(1));
    }

    @Test(expected = TypeMismatchException.class)
    public void constructionShouldThrowIfLowerBoundHasUnknownType() {
        new Summation(new Variable("x", Type.NAT), new Constant("foo"), new Variable("n", Type.NAT), new Number(1));
    }

    @Test(expected = TypeMismatchException.class)
    public void constructionShouldThrowIfUpperBoundHasUnknownType() {
        new Summation(new Variable("x", Type.NAT), new Number(0), new Variable("n", Type.UNKNOWN), new Number(1));
    }

    @Test(expected = TypeMismatchException.class)
    public void constructionShouldThrowIfElementHasUnknownType() {
        new Summation(new Variable("x", Type.NAT), new Number(0), new Variable("n", Type.NAT), new Constant("foo"));
    }

    @Test
    public void constructionShouldNotThrowIfAllPartsHaveNatType() {
        new Summation(new Variable("x", Type.NAT), new Number(0), new Variable("n", Type.NAT),
                new Variable("x", Type.NAT));
    }

}
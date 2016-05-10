package com.ipandora.api.predicate.term;

import org.junit.Test;

public class AdditionTest {

    @Test(expected = TypeMismatchException.class)
    public void constructionShouldThrowIfLeftHasUnknownType() {
        new Addition(new Variable("x", Type.UNKNOWN), new Variable("y", Type.NAT));
    }

    @Test(expected = TypeMismatchException.class)
    public void constructionShouldThrowIfRightHasUnknownType() {
        new Addition(new Variable("x", Type.NAT), new Variable("y", Type.UNKNOWN));
    }

    @Test
    public void constructionShouldNotThrowIfBothHaveNatType() {
        new Addition(new Variable("x", Type.NAT), new Variable("y", Type.NAT));
    }

}
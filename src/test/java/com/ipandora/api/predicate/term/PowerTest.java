package com.ipandora.api.predicate.term;

import org.junit.Test;

public class PowerTest {

    @Test(expected = TypeMismatchException.class)
    public void constructionShouldThrowIfBaseLeftHasUnknownType() {
        new Power(new Variable("x", Type.UNKNOWN), 3);
    }

    @Test
    public void constructionShouldNotThrowIfBaseHasNatType() {
        new Power(new Variable("x", Type.NAT), 3);
    }

}
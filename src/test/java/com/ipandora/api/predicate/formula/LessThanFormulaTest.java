package com.ipandora.api.predicate.formula;

import com.ipandora.api.predicate.term.Addition;
import com.ipandora.api.predicate.term.Type;
import com.ipandora.api.predicate.term.TypeMismatchException;
import com.ipandora.api.predicate.term.Variable;
import org.junit.Test;

public class LessThanFormulaTest {

    @Test(expected = TypeMismatchException.class)
    public void constructionShouldThrowIfLeftHasUnknownType() {
        new LessThanFormula(new Variable("x", Type.UNKNOWN), new Variable("y", Type.NAT));
    }

    @Test(expected = TypeMismatchException.class)
    public void constructionShouldThrowIfRightHasUnknownType() {
        new LessThanFormula(new Variable("x", Type.NAT), new Variable("y", Type.UNKNOWN));
    }

    @Test
    public void constructionShouldNotThrowIfBothHaveNatType() {
        new LessThanFormula(new Variable("x", Type.NAT), new Variable("y", Type.NAT));
    }


}
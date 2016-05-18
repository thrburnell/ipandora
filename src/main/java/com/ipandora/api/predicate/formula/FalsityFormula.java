package com.ipandora.api.predicate.formula;

import com.ipandora.core.formula.FormulaVisitor;

public class FalsityFormula implements Formula {

    @Override
    public <T> T accept(FormulaVisitor<T> visitor) {
        return visitor.visitFalsityFormula(this);
    }

    @Override
    public boolean equals(Object o) {
        return o != null && o instanceof FalsityFormula;
    }

    @Override
    public int hashCode() {
        return "falsity".hashCode();
    }

    @Override
    public String toString() {
        return "\u22A5";
    }
}

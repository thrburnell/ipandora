package com.ipandora.api.predicate.formula;

import com.ipandora.core.formula.FormulaVisitor;

public class TruthFormula implements Formula {

    @Override
    public <T> T accept(FormulaVisitor<T> visitor) {
        return visitor.visitTruthFormula(this);
    }

    @Override
    public boolean equals(Object o) {
        return o != null && o instanceof TruthFormula;
    }

    @Override
    public int hashCode() {
        return "truth".hashCode();
    }

}

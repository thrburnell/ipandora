package com.ipandora.api.predicate.formula;

import com.ipandora.core.formula.FormulaVisitor;

public class FalseFormula implements Formula {

    @Override
    public <T> T accept(FormulaVisitor<T> visitor) {
        return visitor.visitFalseFormula(this);
    }

}

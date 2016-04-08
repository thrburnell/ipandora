package com.ipandora.api.predicate.formula;

import com.ipandora.core.formula.FormulaVisitor;

public class NotFormula implements Formula {

    private final Formula formula;

    public NotFormula(Formula formula) {
        this.formula = formula;
    }

    @Override
    public String toString() {
        return String.format("\u00ac (%s)", formula);
    }

    @Override
    public <T> T accept(FormulaVisitor<T> visitor) {
        return visitor.visitNotFormula(this);
    }

}

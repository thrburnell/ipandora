package com.ipandora.api.predicate.formula;

import com.ipandora.core.formula.FormulaVisitor;

public class NotFormula implements Formula {

    private final Formula formula;

    public NotFormula(Formula formula) {
        this.formula = formula;
    }

    public Formula getFormula() {
        return formula;
    }

    @Override
    public String toString() {
        return String.format("\u00ac (%s)", formula);
    }

    @Override
    public <T> T accept(FormulaVisitor<T> visitor) {
        return visitor.visitNotFormula(this);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        NotFormula that = (NotFormula) o;

        return !(formula != null ? !formula.equals(that.formula) : that.formula != null);

    }

    @Override
    public int hashCode() {
        return formula != null ? 31 * formula.hashCode() : 0;
    }
}

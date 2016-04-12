package com.ipandora.api.predicate.formula;

import com.ipandora.api.predicate.term.Variable;
import com.ipandora.core.formula.FormulaVisitor;

public class ExistsFormula implements Formula {

    private final Variable variable;
    private final Formula formula;

    public ExistsFormula(Variable variable, Formula formula) {
        this.variable = variable;
        this.formula = formula;
    }

    public Variable getVariable() {
        return variable;
    }

    public Formula getFormula() {
        return formula;
    }

    @Override
    public String toString() {
        return String.format("\u2203%s.(%s)", variable, formula);
    }

    @Override
    public <T> T accept(FormulaVisitor<T> visitor) {
        return visitor.visitExistsFormula(this);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        ExistsFormula that = (ExistsFormula) o;

        if (variable != null ? !variable.equals(that.variable) : that.variable != null) return false;
        return !(formula != null ? !formula.equals(that.formula) : that.formula != null);

    }

    @Override
    public int hashCode() {
        int result = variable != null ? variable.hashCode() : 0;
        result = 31 * result + (formula != null ? formula.hashCode() : 0);
        return result;
    }
}

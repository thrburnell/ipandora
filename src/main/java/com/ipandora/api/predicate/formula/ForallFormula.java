package com.ipandora.api.predicate.formula;

import com.ipandora.api.predicate.term.Type;
import com.ipandora.api.predicate.term.Variable;
import com.ipandora.core.formula.FormulaVisitor;

// TODO: generalise ForallFormula to span over multiple variables
public class ForallFormula implements Formula {

    private final Variable variable;
    private final Formula formula;

    public ForallFormula(Variable variable, Formula formula) {
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
        Type type = variable.getType();
        String typeString = type == null ? "" : String.format("\u2208%s", type);
        return String.format("\u2200%s%s.(%s)", variable, typeString, formula);
    }

    @Override
    public <T> T accept(FormulaVisitor<T> visitor) {
        return visitor.visitForallFormula(this);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        ForallFormula that = (ForallFormula) o;

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

package com.ipandora.api.predicate.formula;

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
        return String.format("\u2200%s.(%s)", variable, formula);
    }

    @Override
    public <T> T accept(FormulaVisitor<T> visitor) {
        return visitor.visitForallFormula(this);
    }

}

package com.ipandora.api.predicate.formula;

import com.ipandora.api.predicate.term.Variable;

public class ForallFormula implements Formula {

    private final Variable variable;
    private final Formula formula;

    public ForallFormula(Variable variable, Formula formula) {
        this.variable = variable;
        this.formula = formula;
    }

    @Override
    public String toString() {
        return String.format("\u2200%s.(%s)", variable, formula);
    }

}

package com.ipandora.api.predicate.formula;

import com.ipandora.api.predicate.term.Variable;

public class ExistsFormula implements Formula {

    private final Variable variable;
    private final Formula formula;

    public ExistsFormula(Variable variable, Formula formula) {
        this.variable = variable;
        this.formula = formula;
    }

    @Override
    public String toString() {
        return String.format("\u2203%s.(%s)", variable, formula);
    }

}

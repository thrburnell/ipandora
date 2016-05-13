package com.ipandora.api.predicate.function;

import com.ipandora.api.predicate.formula.Formula;

public class IfCondition implements FunctionCaseCondition {

    private final Formula formula;

    public IfCondition(Formula formula) {
        this.formula = formula;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        IfCondition that = (IfCondition) o;

        return formula.equals(that.formula);
    }

    @Override
    public int hashCode() {
        return formula.hashCode();
    }

}

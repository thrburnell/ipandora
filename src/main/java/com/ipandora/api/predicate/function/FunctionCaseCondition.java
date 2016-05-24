package com.ipandora.api.predicate.function;

import com.ipandora.api.predicate.formula.Formula;

public abstract class FunctionCaseCondition {

    protected final Formula formula;

    protected FunctionCaseCondition(Formula formula) {
        this.formula = formula;
    }

    public Formula getFormula() {
        return formula;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        FunctionCaseCondition that = (FunctionCaseCondition) o;

        return formula.equals(that.formula);
    }

    @Override
    public int hashCode() {
        return formula.hashCode();
    }

}

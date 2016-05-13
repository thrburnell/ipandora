package com.ipandora.api.predicate.function;

import com.ipandora.api.predicate.formula.TruthFormula;

public class OtherwiseCondition implements FunctionCaseCondition {

    @Override
    public boolean equals(Object o) {
        return o != null && o instanceof OtherwiseCondition;
    }

    @Override
    public int hashCode() {
        return "otherwise".hashCode();
    }

}

package com.ipandora.api.predicate.function;

import com.ipandora.api.predicate.formula.TruthFormula;

public class OtherwiseCondition extends FunctionCaseCondition {

    public OtherwiseCondition() {
        super(new TruthFormula());
    }

}

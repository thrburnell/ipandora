package com.ipandora.core.function;

import com.ipandora.api.predicate.formula.ForallFormula;
import com.ipandora.api.predicate.function.FunctionDefinition;

public interface FunctionDefinitionEncoder {

    ForallFormula encode(FunctionDefinition definition);

}

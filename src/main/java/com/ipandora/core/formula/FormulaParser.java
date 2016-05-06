package com.ipandora.core.formula;

import com.ipandora.api.predicate.formula.Formula;

public interface FormulaParser {

    Formula fromString(String formula);

}

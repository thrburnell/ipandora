package com.ipandora.core.formula;

import com.ipandora.api.predicate.formula.Formula;

import java.util.List;

public interface FormulaReducer {

    Formula reduce(List<Formula> formulas);

}

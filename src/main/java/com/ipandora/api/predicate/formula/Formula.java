package com.ipandora.api.predicate.formula;

import com.ipandora.core.formula.FormulaVisitor;

public interface Formula {

    <T> T accept(FormulaVisitor<T> visitor);

}

package com.ipandora.core.z3;

import com.ipandora.core.formula.FormulaVisitor;

public interface SMTGeneratingFormulaVisitor extends FormulaVisitor<String> {

    String getPredicateDefinitions();
    String getTypeDefinition();

}

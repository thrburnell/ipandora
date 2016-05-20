package com.ipandora.core.z3;

import com.ipandora.core.formula.FormulaVisitor;

import java.util.Map;
import java.util.Set;

public interface SMTGeneratingFormulaVisitor extends FormulaVisitor<String> {

    Map<String, Integer> getPredicateNamesToArgCount();
    Set<String> getPropositionNames();
    Set<String> getConstantNames();
    Map<String, Integer> getFunctionNamesToArgCount();

}

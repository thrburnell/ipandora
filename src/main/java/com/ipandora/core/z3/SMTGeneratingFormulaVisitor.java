package com.ipandora.core.z3;

import com.ipandora.api.predicate.function.FunctionPrototype;
import com.ipandora.api.predicate.formula.PredicatePrototype;
import com.ipandora.api.predicate.term.Type;
import com.ipandora.core.formula.FormulaVisitor;

import java.util.List;
import java.util.Map;
import java.util.Set;

public interface SMTGeneratingFormulaVisitor extends FormulaVisitor<String> {

    List<PredicatePrototype> getPredicatePrototypes();
    Set<String> getPropositionNames();
    Map<String, Type> getConstantNamesToTypes();
    List<FunctionPrototype> getFunctionPrototypes();

}

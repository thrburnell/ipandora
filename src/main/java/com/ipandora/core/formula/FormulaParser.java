package com.ipandora.core.formula;

import com.ipandora.api.predicate.formula.Formula;
import com.ipandora.api.predicate.function.FunctionPrototype;

import java.util.List;

public interface FormulaParser {

    Formula fromString(String formula) throws FormulaParsingException;
    Formula fromString(String formula, List<FunctionPrototype> functionPrototypes) throws FormulaParsingException;

    Formula fromStringWithTypeChecking(String formula) throws FormulaParsingException;
    Formula fromStringWithTypeChecking(String formula, List<FunctionPrototype> functionPrototypes)
            throws FormulaParsingException;

}

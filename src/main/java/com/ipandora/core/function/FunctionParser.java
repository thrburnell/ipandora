package com.ipandora.core.function;

import com.ipandora.api.predicate.function.FunctionDefinition;
import com.ipandora.api.predicate.function.FunctionPrototype;

import java.util.List;

public interface FunctionParser {

    FunctionDefinition fromString(String function) throws FunctionParsingException;
    FunctionDefinition fromString(String function, List<FunctionPrototype> functionPrototypes)
            throws FunctionParsingException;

    FunctionDefinition fromStringWithTypeChecking(String function) throws FunctionParsingException;
    FunctionDefinition fromStringWithTypeChecking(String function, List<FunctionPrototype> functionPrototypes)
            throws FunctionParsingException;

}

package com.ipandora.core.function;

import com.ipandora.api.predicate.function.FunctionDefinition;

public interface FunctionParser {

    FunctionDefinition fromString(String function) throws FunctionParsingException;
    FunctionDefinition fromStringWithTypeChecking(String function) throws FunctionParsingException;

}

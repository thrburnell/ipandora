package com.ipandora.core.function;

import com.ipandora.api.predicate.function.Function;

public interface FunctionParser {

    Function fromString(String function) throws FunctionParsingException;
    Function fromStringWithTypeChecking(String function) throws FunctionParsingException;

}

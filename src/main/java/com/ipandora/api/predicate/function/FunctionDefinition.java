package com.ipandora.api.predicate.function;

import com.ipandora.core.function.FunctionDefinitionVisitor;

public interface FunctionDefinition {

    <T> T accept(FunctionDefinitionVisitor<T> visitor);

}

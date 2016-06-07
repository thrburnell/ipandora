package com.ipandora.api.predicate.function;

import com.ipandora.api.predicate.term.Type;
import com.ipandora.api.predicate.term.Variable;
import com.ipandora.core.function.FunctionDefinitionVisitor;

import java.util.List;

public interface FunctionDefinition {

    String getName();
    List<Variable> getArguments();
    List<FunctionCase> getCases();
    Type getReturnType();

    <T> T accept(FunctionDefinitionVisitor<T> visitor);

}

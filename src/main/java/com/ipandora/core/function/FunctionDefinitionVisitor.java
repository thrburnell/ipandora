package com.ipandora.core.function;

import com.ipandora.api.predicate.function.FunctionDefinition;
import com.ipandora.api.predicate.function.MathematicalFunctionDefinition;

public interface FunctionDefinitionVisitor<T> {

    T visit(FunctionDefinition function);
    T visitMathematicalFunctionDefinition(MathematicalFunctionDefinition mathematicalFunction);

}

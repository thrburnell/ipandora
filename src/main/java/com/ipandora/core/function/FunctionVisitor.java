package com.ipandora.core.function;

import com.ipandora.api.predicate.function.Function;
import com.ipandora.api.predicate.function.MathematicalFunction;

public interface FunctionVisitor<T> {

    T visit(Function function);
    T visitMathematicalFunction(MathematicalFunction mathematicalFunction);

}

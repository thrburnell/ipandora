package com.ipandora.api.predicate.function;

import com.ipandora.core.function.FunctionVisitor;

public interface Function {

    <T> T accept(FunctionVisitor<T> visitor);

}

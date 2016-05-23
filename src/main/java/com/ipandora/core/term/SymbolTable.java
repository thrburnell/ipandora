package com.ipandora.core.term;

import com.ipandora.api.predicate.term.FunctionPrototype;
import com.ipandora.api.predicate.term.Type;

public interface SymbolTable {

    void setParent(SymbolTable parent);
    SymbolTable getParent();

    Type getType(String variable);
    FunctionPrototype getFunctionPrototype(String functionName);

    void addMapping(String variable, Type type);
    void addMapping(String variable, FunctionPrototype prototype);

}

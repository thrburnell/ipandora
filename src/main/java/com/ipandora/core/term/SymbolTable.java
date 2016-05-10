package com.ipandora.core.term;

import com.ipandora.api.predicate.term.Type;

public interface SymbolTable {

    void setParent(SymbolTable parent);
    SymbolTable getParent();
    Type getType(String variable);
    void addMapping(String variable, Type type);

}

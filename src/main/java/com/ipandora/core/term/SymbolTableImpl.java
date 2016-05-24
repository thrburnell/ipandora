package com.ipandora.core.term;

import com.ipandora.api.predicate.function.FunctionPrototype;
import com.ipandora.api.predicate.term.Type;

import java.util.HashMap;
import java.util.Map;

public class SymbolTableImpl implements SymbolTable {

    private final Map<String, Type> typeMapping = new HashMap<>();
    private final Map<String, FunctionPrototype> prototypeMapping = new HashMap<>();
    private SymbolTable parent;

    @Override
    public void setParent(SymbolTable parent) {
        this.parent = parent;
    }

    @Override
    public SymbolTable getParent() {
        return parent;
    }

    @Override
    public Type getType(String variable) {
        Type type = typeMapping.get(variable);
        if (type != null) {
            return type;
        }

        if (parent != null) {
            return parent.getType(variable);
        }

        return null;
    }

    @Override
    public void addMapping(String variable, Type type) {
        typeMapping.put(variable, type);
    }

    @Override
    public void addMapping(String variable, FunctionPrototype prototype) {
        prototypeMapping.put(variable, prototype);
    }

    @Override
    public FunctionPrototype getFunctionPrototype(String functionName) {
        FunctionPrototype prototype = prototypeMapping.get(functionName);
        if (prototype != null) {
            return prototype;
        }

        if (parent != null) {
            return parent.getFunctionPrototype(functionName);
        }

        return null;
    }

}

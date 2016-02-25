package com.ipandora.api.predicate.term;

public class Variable implements Term {

    private final String name;

    public Variable(String name) {
        this.name = name;
    }

    @Override
    public String toString() {
        return name;
    }

}

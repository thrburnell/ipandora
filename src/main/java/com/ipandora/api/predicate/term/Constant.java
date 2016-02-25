package com.ipandora.api.predicate.term;

public class Constant implements Term {

    private final String name;

    public Constant(String name) {
        this.name = name;
    }

    @Override
    public String toString() {
        return name;
    }

}

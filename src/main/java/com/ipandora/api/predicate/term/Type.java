package com.ipandora.api.predicate.term;

public enum Type implements Comparable<Type> {

    // NOTE: UNKNOWN must be kept last, for natural ordering
    NAT("Nat"),
    UNKNOWN("Unknown");

    private final String name;

    Type(String name) {
        this.name = name;
    }

    public String toString() {
        return name;
    }

    public String getName() {
        return name;
    }
}

package com.ipandora.api.predicate.term;

public enum Type {

    NAT("Nat"), UNKNOWN("");

    private final String name;

    Type(String name) {
        this.name = name;
    }

    public String toString() {
        return name;
    }

}

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

    public static Type withIdentifier(String identifier) {
        for (Type type : values()) {
            if (type.getName().equals(identifier)) {
                return type;
            }
        }

        throw new IllegalArgumentException("No Type for given identifier: " + identifier);
    }

}

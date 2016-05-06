package com.ipandora.api.predicate.term;

import com.ipandora.core.term.TermVisitor;

public class Constant implements Term {

    private final String name;

    public Constant(String name) {
        this.name = name;
    }

    public String getName() {
        return name;
    }

    @Override
    public <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitConstant(this);
    }

    @Override
    public String toString() {
        return name;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        Constant constant = (Constant) o;

        return name.equals(constant.name);
    }

    @Override
    public int hashCode() {
        return name.hashCode();
    }

}

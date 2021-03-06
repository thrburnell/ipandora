package com.ipandora.api.predicate.term;

import com.ipandora.core.term.TermVisitor;

public class Constant implements Atom {

    private final String name;
    private Type type;

    public Constant(String name) {
        this(name, Type.UNKNOWN);
    }

    public Constant(String name, Type type) {
        this.name = name;
        this.type = type;
    }

    public String getName() {
        return name;
    }

    @Override
    public <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitConstant(this);
    }

    @Override
    public void setType(Type type) {
        this.type = type;
    }

    @Override
    public Type getType() {
        return type;
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

        if (!name.equals(constant.name)) return false;
        return type == constant.type;
    }

    @Override
    public int hashCode() {
        int result = name.hashCode();
        result = 31 * result + type.hashCode();
        return result;
    }

}

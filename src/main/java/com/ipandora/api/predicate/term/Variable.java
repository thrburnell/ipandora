package com.ipandora.api.predicate.term;

import com.ipandora.core.term.TermVisitor;

public class Variable implements Atom {

    private final String name;
    private Type type;

    public Variable(String name) {
        this(name, Type.UNKNOWN);
    }

    public Variable(String name, Type type) {
        this.name = name;
        this.type = type;
    }

    public String getName() {
        return name;
    }

    public static Variable withTypeNat(String name) {
        return new Variable(name, Type.NAT);
    }

    @Override
    public <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitVariable(this);
    }

    @Override
    public Type getType() {
        return type;
    }

    @Override
    public void setType(Type type) {
        this.type = type;
    }

    @Override
    public String toString() {
        return name;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        Variable variable = (Variable) o;

        if (!name.equals(variable.name)) return false;
        return type == variable.type;
    }

    @Override
    public int hashCode() {
        int result = name.hashCode();
        result = 31 * result + type.hashCode();
        return result;
    }

}

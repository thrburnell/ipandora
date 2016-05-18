package com.ipandora.api.predicate.term;

import com.ipandora.core.term.TermVisitor;

public class Number implements Atom {

    private final int number;
    private final Type type;

    public Number(int number) {
        this.number = number;
        this.type = Type.NAT;
    }

    public int getNumber() {
        return number;
    }

    @Override
    public <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitNumber(this);
    }

    @Override
    public Type getType() {
        return type;
    }

    @Override
    public String toString() {
        return String.valueOf(number);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        Number number1 = (Number) o;

        if (number != number1.number) return false;
        return type == number1.type;
    }

    @Override
    public int hashCode() {
        int result = number;
        result = 31 * result + type.hashCode();
        return result;
    }
}

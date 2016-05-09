package com.ipandora.api.predicate.term;

import com.ipandora.core.term.TermVisitor;

public class Number implements Term {

    private final int number;

    public Number(int number) {
        this.number = number;
    }

    public int getNumber() {
        return number;
    }

    @Override
    public <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitNumber(this);
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

        return number == number1.number;
    }

    @Override
    public int hashCode() {
        return number;
    }

}

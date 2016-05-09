package com.ipandora.api.predicate.term;

import com.ipandora.core.term.TermVisitor;

public class Power implements Term {

    private final Term base;
    private final int exponent;

    public Power(Term base, int exponent) {
        this.base = base;
        this.exponent = exponent;
    }

    public Term getBase() {
        return base;
    }

    public int getExponent() {
        return exponent;
    }

    @Override
    public <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitPower(this);
    }

    @Override
    public String toString() {
        return String.format("(%s ^ %d)", base, exponent);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        Power power1 = (Power) o;

        if (exponent != power1.exponent) return false;
        return base.equals(power1.base);
    }

    @Override
    public int hashCode() {
        int result = base.hashCode();
        result = 31 * result + exponent;
        return result;
    }

}

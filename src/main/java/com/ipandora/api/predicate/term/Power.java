package com.ipandora.api.predicate.term;

import com.ipandora.core.term.TermVisitor;

public class Power implements Term {

    private final Term base;
    private final int exponent;
    private final Type type;

    public Power(Term base, int exponent) {
        this.base = base;
        this.exponent = exponent;
        this.type = Type.NAT;
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
    public Type getType() {
        return type;
    }

    @Override
    public String toString() {
        return String.format("(%s ^ %d)", base, exponent);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        Power power = (Power) o;

        if (exponent != power.exponent) return false;
        if (!base.equals(power.base)) return false;
        return type == power.type;
    }

    @Override
    public int hashCode() {
        int result = base.hashCode();
        result = 31 * result + exponent;
        result = 31 * result + type.hashCode();
        return result;
    }

}

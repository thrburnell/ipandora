package com.ipandora.api.predicate.term;

import com.ipandora.core.term.TermVisitor;

public class Summation implements Term {

    private final Variable variable;
    private final Term lowerBound;
    private final Term upperBound;
    private final Term element;

    public Summation(Variable variable, Term lowerBound, Term upperBound, Term element) {
        this.variable = variable;
        this.lowerBound = lowerBound;
        this.upperBound = upperBound;
        this.element = element;
    }

    @Override
    public <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitSummation(this);
    }

    @Override
    public String toString() {
        return String.format("(\u03a3 {%s=%s..%s} %s)", variable, lowerBound, upperBound, element);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        Summation summation = (Summation) o;

        if (!variable.equals(summation.variable)) return false;
        if (!lowerBound.equals(summation.lowerBound)) return false;
        if (!upperBound.equals(summation.upperBound)) return false;
        return element.equals(summation.element);
    }

    @Override
    public int hashCode() {
        int result = variable.hashCode();
        result = 31 * result + lowerBound.hashCode();
        result = 31 * result + upperBound.hashCode();
        result = 31 * result + element.hashCode();
        return result;
    }

}

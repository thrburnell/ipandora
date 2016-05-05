package com.ipandora.api.predicate.formula;

import com.ipandora.core.formula.FormulaVisitor;

public class PropositionFormula implements Formula {

    private final String name;

    public PropositionFormula(String name) {
        this.name = name;
    }

    public String getName() {
        return name;
    }

    @Override
    public <T> T accept(FormulaVisitor<T> visitor) {
        return visitor.visitPropositionFormula(this);
    }

    @Override
    public String toString() {
        return name;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        PropositionFormula that = (PropositionFormula) o;

        return name.equals(that.name);
    }

    @Override
    public int hashCode() {
        return name.hashCode();
    }
}

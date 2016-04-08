package com.ipandora.api.predicate.formula;

import com.ipandora.core.formula.FormulaVisitor;

public class AtomFormula implements Formula {

    private final String identifier;

    public AtomFormula(String identifier) {
        this.identifier = identifier;
    }

    @Override
    public <T> T accept(FormulaVisitor<T> visitor) {
        return visitor.visitAtomFormula(this);
    }
}

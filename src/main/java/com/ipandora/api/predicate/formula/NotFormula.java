package com.ipandora.api.predicate.formula;

public class NotFormula implements Formula {

    private final Formula formula;

    public NotFormula(Formula formula) {
        this.formula = formula;
    }

    @Override
    public String toString() {
        return String.format("\u00ac (%s)", formula);
    }

}

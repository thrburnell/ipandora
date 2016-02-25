package com.ipandora.api.predicate;

import com.fasterxml.jackson.annotation.JsonProperty;

public class FormulaString {

    private String formula;

    public FormulaString() {
        // default constructor for serializer
    }

    public FormulaString(String formula) {
        this.formula = formula;
    }

    @JsonProperty
    public String getFormula() {
        return formula;
    }

    @JsonProperty
    public void setFormula(String formula) {
        this.formula = formula;
    }
}

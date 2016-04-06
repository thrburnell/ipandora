package com.ipandora.api.predicate.validate;

import com.fasterxml.jackson.annotation.JsonProperty;

public class ValidateRequest {

    private String formula;

    @JsonProperty
    public String getFormula() {
        return formula;
    }

    @JsonProperty
    public void setFormula(String formula) {
        this.formula = formula;
    }
}

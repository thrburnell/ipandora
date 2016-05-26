package com.ipandora.api.predicate.validate;

import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.annotation.JsonProperty;

@JsonInclude(JsonInclude.Include.NON_NULL)
public class ValidateResponse {

    private String formula;
    private boolean valid;
    private String errorMsg;

    @JsonProperty
    public String getFormula() {
        return formula;
    }

    @JsonProperty
    public void setFormula(String formula) {
        this.formula = formula;
    }

    @JsonProperty
    public boolean isValid() {
        return valid;
    }

    @JsonProperty
    public void setValid(boolean valid) {
        this.valid = valid;
    }

    @JsonProperty
    public String getErrorMsg() {
        return errorMsg;
    }

    @JsonProperty
    public void setErrorMsg(String errorMsg) {
        this.errorMsg = errorMsg;
    }

}

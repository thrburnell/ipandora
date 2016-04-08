package com.ipandora.api.predicate.validate;

import com.fasterxml.jackson.annotation.JsonInclude;

@JsonInclude(JsonInclude.Include.NON_NULL)
public class ValidateResponse {

    private String formula;
    private boolean syntaxValid;
    private String errorMsg;

    public String getFormula() {
        return formula;
    }

    public void setFormula(String formula) {
        this.formula = formula;
    }

    public boolean isSyntaxValid() {
        return syntaxValid;
    }

    public void setSyntaxValid(boolean syntaxValid) {
        this.syntaxValid = syntaxValid;
    }

    public String getErrorMsg() {
        return errorMsg;
    }

    public void setErrorMsg(String errorMsg) {
        this.errorMsg = errorMsg;
    }

}

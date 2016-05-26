package com.ipandora.api.predicate.validate;

import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.annotation.JsonProperty;
import com.ipandora.api.predicate.function.FunctionPrototypeRequest;

@JsonInclude(JsonInclude.Include.NON_NULL)
public class ValidateFunctionResponse {

    private String function;
    private boolean valid;
    private FunctionPrototypeRequest prototype;
    private String errorMsg;

    @JsonProperty
    public String getFunction() {
        return function;
    }

    @JsonProperty
    public void setFunction(String function) {
        this.function = function;
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
    public FunctionPrototypeRequest getPrototype() {
        return prototype;
    }

    @JsonProperty
    public void setPrototype(FunctionPrototypeRequest prototype) {
        this.prototype = prototype;
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

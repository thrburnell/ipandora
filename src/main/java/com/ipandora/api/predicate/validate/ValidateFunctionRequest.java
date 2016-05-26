package com.ipandora.api.predicate.validate;

import com.fasterxml.jackson.annotation.JsonProperty;

public class ValidateFunctionRequest {

    private String function;

    @JsonProperty
    public String getFunction() {
        return function;
    }

    @JsonProperty
    public void setFunction(String function) {
        this.function = function;
    }

}

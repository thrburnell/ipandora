package com.ipandora.api.predicate.function;

import com.fasterxml.jackson.annotation.JsonProperty;

import java.util.List;

public class FunctionPrototypeRequest {

    private String name;
    private List<String> argTypes;
    private String returnType;

    @JsonProperty
    public String getName() {
        return name;
    }

    @JsonProperty
    public void setName(String name) {
        this.name = name;
    }

    @JsonProperty
    public List<String> getArgTypes() {
        return argTypes;
    }

    @JsonProperty
    public void setArgTypes(List<String> argTypes) {
        this.argTypes = argTypes;
    }

    @JsonProperty
    public String getReturnType() {
        return returnType;
    }

    @JsonProperty
    public void setReturnType(String returnType) {
        this.returnType = returnType;
    }

}

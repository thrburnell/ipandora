package com.ipandora.api.predicate.proofstep;

import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.annotation.JsonProperty;
import com.ipandora.api.predicate.function.FunctionPrototypeRequest;

import java.util.List;

@JsonInclude(JsonInclude.Include.NON_NULL)
public class StepResponse {

    private String method;
    private String goal;
    private String from;
    private List<String> assumptions;
    private String function;
    private List<FunctionPrototypeRequest> functions;
    private Boolean valid;
    private String errorMsg;

    @JsonProperty
    public String getMethod() {
        return method;
    }

    @JsonProperty
    public void setMethod(String method) {
        this.method = method;
    }

    @JsonProperty
    public String getGoal() {
        return goal;
    }

    @JsonProperty
    public void setGoal(String goal) {
        this.goal = goal;
    }

    @JsonProperty
    public String getFrom() {
        return from;
    }

    @JsonProperty
    public void setFrom(String from) {
        this.from = from;
    }

    @JsonProperty
    public List<String> getAssumptions() {
        return assumptions;
    }

    @JsonProperty
    public void setAssumptions(List<String> assumptions) {
        this.assumptions = assumptions;
    }

    @JsonProperty
    public String getFunction() {
        return function;
    }

    @JsonProperty
    public void setFunction(String function) {
        this.function = function;
    }

    @JsonProperty
    public List<FunctionPrototypeRequest> getFunctions() {
        return functions;
    }

    @JsonProperty
    public void setFunctions(List<FunctionPrototypeRequest> functions) {
        this.functions = functions;
    }

    @JsonProperty
    public Boolean isValid() {
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

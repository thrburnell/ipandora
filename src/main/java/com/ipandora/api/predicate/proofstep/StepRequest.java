package com.ipandora.api.predicate.proofstep;

import com.fasterxml.jackson.annotation.JsonProperty;

import java.util.List;

public class StepRequest {

    private String method;
    private String goal;
    private String from;

    private List<String> assumptions;

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

}

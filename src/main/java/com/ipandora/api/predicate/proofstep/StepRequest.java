package com.ipandora.api.predicate.proofstep;

import com.fasterxml.jackson.annotation.JsonProperty;

import java.util.List;

public class StepRequest {

    private List<String> assumptions;
    private String goal;

    @JsonProperty
    public List<String> getAssumptions() {
        return assumptions;
    }

    @JsonProperty
    public void setAssumptions(List<String> assumptions) {
        this.assumptions = assumptions;
    }

    @JsonProperty
    public String getGoal() {
        return goal;
    }

    @JsonProperty
    public void setGoal(String goal) {
        this.goal = goal;
    }

}

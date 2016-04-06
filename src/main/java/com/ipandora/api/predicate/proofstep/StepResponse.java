package com.ipandora.api.predicate.proofstep;

import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.annotation.JsonProperty;

import java.util.List;

@JsonInclude(JsonInclude.Include.NON_NULL)
public class StepResponse {

    private List<String> assumptions;
    private String goal;
    private boolean validityPreserved;
    private String errorMsg;

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

    @JsonProperty
    public boolean isValidityPreserved() {
        return validityPreserved;
    }

    @JsonProperty
    public void setValidityPreserved(boolean validityPreserved) {
        this.validityPreserved = validityPreserved;
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

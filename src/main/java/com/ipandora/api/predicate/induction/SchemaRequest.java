package com.ipandora.api.predicate.induction;

import com.fasterxml.jackson.annotation.JsonProperty;

public class SchemaRequest {

    private String goal;
    private String variable;

    @JsonProperty
    public String getGoal() {
        return goal;
    }

    @JsonProperty
    public void setGoal(String goal) {
        this.goal = goal;
    }

    @JsonProperty
    public String getVariable() {
        return variable;
    }

    @JsonProperty
    public void setVariable(String variable) {
        this.variable = variable;
    }
}

package com.ipandora.api.predicate.induction;

import com.fasterxml.jackson.annotation.JsonProperty;

public class SchemaRequest {

    private String goal;

    @JsonProperty
    public String getGoal() {
        return goal;
    }

    @JsonProperty
    public void setGoal(String goal) {
        this.goal = goal;
    }

}

package com.ipandora.api.predicate.induction;

import com.fasterxml.jackson.annotation.JsonProperty;
import com.ipandora.api.predicate.function.FunctionPrototypeRequest;

import java.util.List;

public class SchemaRequest {

    private String goal;
    private String variable;
    private List<FunctionPrototypeRequest> functions;

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

    @JsonProperty
    public List<FunctionPrototypeRequest> getFunctions() {
        return functions;
    }

    @JsonProperty
    public void setFunctions(List<FunctionPrototypeRequest> functions) {
        this.functions = functions;
    }

}

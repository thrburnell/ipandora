package com.ipandora.api.predicate.induction;

import com.fasterxml.jackson.annotation.JsonProperty;

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

    public static class FunctionPrototypeRequest {

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

}

package com.ipandora.api.predicate.induction;

import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.annotation.JsonProperty;
import com.ipandora.api.predicate.function.FunctionPrototypeRequest;

import java.util.List;

@JsonInclude(JsonInclude.Include.NON_NULL)
public class SchemaResponse {

    private String goal;
    private String variable;
    private List<FunctionPrototypeRequest> functions;
    private BaseCase baseCase;
    private InductiveCase inductiveCase;
    private String errorMsg;

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

    @JsonProperty
    public BaseCase getBaseCase() {
        return baseCase;
    }

    @JsonProperty
    public void setBaseCase(BaseCase baseCase) {
        this.baseCase = baseCase;
    }

    @JsonProperty
    public InductiveCase getInductiveCase() {
        return inductiveCase;
    }

    @JsonProperty
    public void setInductiveCase(InductiveCase inductiveCase) {
        this.inductiveCase = inductiveCase;
    }

    @JsonProperty
    public String getErrorMsg() {
        return errorMsg;
    }

    @JsonProperty
    public void setErrorMsg(String errorMsg) {
        this.errorMsg = errorMsg;
    }


    public static class InductiveVariable {

        private String name;
        private String domain;

        @JsonProperty
        public String getName() {
            return name;
        }

        @JsonProperty
        public void setName(String name) {
            this.name = name;
        }

        @JsonProperty
        public String getDomain() {
            return domain;
        }

        @JsonProperty
        public void setDomain(String domain) {
            this.domain = domain;
        }
    }

    public static class BaseCase {

        private List<String> toShow;

        @JsonProperty
        public List<String> getToShow() {
            return toShow;
        }

        @JsonProperty
        public void setToShow(List<String> toShow) {
            this.toShow = toShow;
        }
    }

    public static class InductiveCase {

        private InductiveVariable arbitrary;
        private String hypothesis;
        private List<String> toShow;

        @JsonProperty
        public InductiveVariable getArbitrary() {
            return arbitrary;
        }

        @JsonProperty
        public void setArbitrary(InductiveVariable arbitrary) {
            this.arbitrary = arbitrary;
        }

        @JsonProperty
        public String getHypothesis() {
            return hypothesis;
        }

        @JsonProperty
        public void setHypothesis(String hypothesis) {
            this.hypothesis = hypothesis;
        }

        @JsonProperty
        public List<String> getToShow() {
            return toShow;
        }

        @JsonProperty
        public void setToShow(List<String> toShow) {
            this.toShow = toShow;
        }
    }
}

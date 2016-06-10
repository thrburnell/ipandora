package com.ipandora.api.predicate.proofstep;

import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.annotation.JsonProperty;

@JsonInclude(JsonInclude.Include.NON_NULL)
public class ExhaustiveCasesResponse {

    private String first;
    private String second;
    private Boolean exhaustive;
    private String errorMsg;

    @JsonProperty
    public String getFirst() {
        return first;
    }

    @JsonProperty
    public void setFirst(String first) {
        this.first = first;
    }

    @JsonProperty
    public String getSecond() {
        return second;
    }

    @JsonProperty
    public void setSecond(String second) {
        this.second = second;
    }

    @JsonProperty
    public Boolean getExhaustive() {
        return exhaustive;
    }

    @JsonProperty
    public void setExhaustive(Boolean exhaustive) {
        this.exhaustive = exhaustive;
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

package com.ipandora.api.predicate.proofstep;

import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.annotation.JsonProperty;

@JsonInclude(JsonInclude.Include.NON_NULL)
public class EquivalentResponse {

    private String first;
    private String second;
    private Boolean equivalent;
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
    public Boolean getEquivalent() {
        return equivalent;
    }

    @JsonProperty
    public void setEquivalent(Boolean equivalent) {
        this.equivalent = equivalent;
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

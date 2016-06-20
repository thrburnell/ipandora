package com.ipandora.api.predicate.proofstep;

import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.annotation.JsonProperty;

@JsonInclude(JsonInclude.Include.NON_NULL)
public class TermEqualStructureResponse {

    private String first;
    private String second;
    private Boolean equal;
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
    public Boolean getEqual() {
        return equal;
    }

    @JsonProperty
    public void setEqual(Boolean equivalent) {
        this.equal = equivalent;
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

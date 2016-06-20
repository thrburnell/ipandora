package com.ipandora.api.predicate.proofstep;

import com.fasterxml.jackson.annotation.JsonProperty;

public class TermEqualStructureRequest {

    private String first;
    private String second;

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

}

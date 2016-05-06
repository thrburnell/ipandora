package com.ipandora.api.predicate.read;

import com.fasterxml.jackson.annotation.JsonProperty;

import java.util.List;

public class ReadResponse {

    private List<String> given;
    private List<String> toShow;

    @JsonProperty
    public List<String> getGiven() {
        return given;
    }

    @JsonProperty
    public void setGiven(List<String> given) {
        this.given = given;
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

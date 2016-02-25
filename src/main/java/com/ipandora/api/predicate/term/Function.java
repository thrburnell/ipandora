package com.ipandora.api.predicate.term;

import java.util.List;

public class Function implements Term {

    private final String name;
    private final List<Term> params;

    public Function(String name, List<Term> params) {
        this.name = name;
        this.params = params;
    }

}

package com.ipandora.core.z3;

import com.ipandora.api.predicate.term.Type;

public enum Z3Sort {

    INT("Int"),
    BOOL("Bool"),
    ARBITRARY("Type");

    private final String code;

    Z3Sort(String code) {
        this.code = code;
    }

    public String getCode() {
        return code;
    }

    public static Z3Sort forType(Type type) throws Z3TranslationException {

        switch (type) {
            case NAT:     return INT;
            case UNKNOWN: return ARBITRARY;
        }

        throw new Z3TranslationException("No known Z3 type for term type: " + type);
    }

}

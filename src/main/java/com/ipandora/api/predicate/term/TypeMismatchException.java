package com.ipandora.api.predicate.term;

import com.ipandora.core.formula.SemanticAnalysisException;

public class TypeMismatchException extends SemanticAnalysisException {

    public TypeMismatchException(String message) {
        super(message);
    }

}

package com.ipandora.core.proof;

import com.ipandora.api.predicate.function.FunctionDefinition;
import com.ipandora.api.predicate.term.Term;

public interface FunctionEqualityChecker {

    boolean check(Term t1, Term t2, FunctionDefinition functionDefinition) throws ProofStepCheckException;

}

package com.ipandora.core.proof;

import com.ipandora.api.predicate.term.Term;

public interface ArithmeticEqualityChecker {

    /**
     * Checks if the given Terms are equal by arithmetic. This is true if t1 = t2 holds for all possible assignments
     * to the variables, constants and functions in the terms.
     */
    boolean check(Term t1, Term t2) throws ProofStepCheckException;

}

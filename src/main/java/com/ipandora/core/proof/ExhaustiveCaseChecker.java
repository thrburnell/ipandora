package com.ipandora.core.proof;

import com.ipandora.api.predicate.formula.Formula;

public interface ExhaustiveCaseChecker {


    boolean check(Formula f1, Formula f2) throws ProofStepCheckException;

}

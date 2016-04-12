package com.ipandora.core.formula;

import com.ipandora.api.predicate.formula.Formula;

import java.util.List;

public interface ImpliesChecker {

    boolean check(List<Formula> assumptions, Formula goal) throws ImpliesCheckerException;

}

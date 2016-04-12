package com.ipandora.core.z3;

import com.ipandora.api.predicate.formula.Formula;

public interface SMTCodeGenerator {

    String generateCheckSatCode(Formula formula);

}

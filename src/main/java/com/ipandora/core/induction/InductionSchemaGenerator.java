package com.ipandora.core.induction;

import com.ipandora.api.predicate.formula.ForallFormula;
import com.ipandora.api.predicate.term.Variable;

public interface InductionSchemaGenerator {

    InductionSchema generateSchema(ForallFormula forallFormula, Variable variable) throws SchemaGeneratorException;

}

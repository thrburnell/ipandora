package com.ipandora.core.induction;

import com.ipandora.api.predicate.formula.ForallFormula;

public interface InductionSchemaGenerator {

    InductionSchema generateSchema(ForallFormula forallFormula) throws SchemaGeneratorException;

}

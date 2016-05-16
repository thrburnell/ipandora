package com.ipandora.core.induction;

import com.ipandora.api.predicate.formula.ForallFormula;
import com.ipandora.api.predicate.formula.Formula;
import com.ipandora.api.predicate.term.*;
import com.ipandora.api.predicate.term.Number;
import com.ipandora.core.formula.TermSubstitutor;

import java.util.Collections;

public class MathematicalInductionSchemaGenerator implements InductionSchemaGenerator {

    private final TermSubstitutor termSubstitutor;

    public MathematicalInductionSchemaGenerator(TermSubstitutor termSubstitutor) {
        this.termSubstitutor = termSubstitutor;
    }

    @Override
    public InductionSchema generateSchema(ForallFormula forallFormula) throws SchemaGeneratorException {

        Variable variable = forallFormula.getVariable();
        Formula formula = forallFormula.getFormula();

        if (variable.getType() != Type.NAT) {
            throw new SchemaGeneratorException("Cannot generate induction schema for variable of non-Nat type: " +
                    variable);
        }

        Formula baseCase = termSubstitutor.cloneAndSubstituteInScope(formula, variable, new Number(0));
        Constant k = new Constant("k"); // TODO: make sure "k" doesn't clash with formula
        Formula indHyp = termSubstitutor.cloneAndSubstituteInScope(formula, variable, k);
        Formula indCase = termSubstitutor.cloneAndSubstituteInScope(formula, variable, new Addition(k, new Number(1)));

        return new InductionSchema(Collections.singletonList(baseCase), k, indHyp, Collections.singletonList(indCase));
    }

}

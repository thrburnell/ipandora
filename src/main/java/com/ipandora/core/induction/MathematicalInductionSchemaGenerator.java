package com.ipandora.core.induction;

import com.ipandora.api.predicate.formula.ForallFormula;
import com.ipandora.api.predicate.formula.Formula;
import com.ipandora.api.predicate.term.*;
import com.ipandora.api.predicate.term.Number;
import com.ipandora.core.formula.AtomicTermCollector;
import com.ipandora.core.formula.TermSubstitutor;
import com.ipandora.core.term.TermStringBuilder;

import java.util.Collections;
import java.util.Set;

public class MathematicalInductionSchemaGenerator implements InductionSchemaGenerator {

    public static final String DEFAULT_INDUCTIVE_TERM_NAME = "k";
    public static final int SPECIAL_INDUCTIVE_TERM_NAME_INITIAL_SUFFIX = 1;

    private final TermSubstitutor termSubstitutor;
    private final AtomicTermCollector atomicTermCollector;
    private final TermStringBuilder termStringBuilder;

    public MathematicalInductionSchemaGenerator(TermStringBuilder termStringBuilder,
                                                AtomicTermCollector atomicTermCollector,
                                                TermSubstitutor termSubstitutor) {
        this.termStringBuilder = termStringBuilder;
        this.termSubstitutor = termSubstitutor;
        this.atomicTermCollector = atomicTermCollector;
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
        Constant k = getConstantWithNewName(formula);
        Formula indHyp = termSubstitutor.cloneAndSubstituteInScope(formula, variable, k);
        Formula indCase = termSubstitutor.cloneAndSubstituteInScope(formula, variable, new Addition(k, new Number(1)));

        return new InductionSchema(Collections.singletonList(baseCase), k, indHyp, Collections.singletonList(indCase));
    }

    private Constant getConstantWithNewName(Formula formula) {

        Set<Atom> atoms = atomicTermCollector.collectAtoms(formula);

        // Try to use k by default
        String name = DEFAULT_INDUCTIVE_TERM_NAME;
        if (atomSetContainsAtomWithName(atoms, name)) {
            int suffix = SPECIAL_INDUCTIVE_TERM_NAME_INITIAL_SUFFIX;
            while (atomSetContainsAtomWithName(atoms, (name = String.format("k%d", suffix)))) {
                suffix++;
            }
        }

        return new Constant(name);
    }

    private boolean atomSetContainsAtomWithName(Set<Atom> atoms, String name) {

        for (Atom atom : atoms) {
            if (termStringBuilder.build(atom).equals(name)) {
                return true;
            }
        }

        return false;
    }

}

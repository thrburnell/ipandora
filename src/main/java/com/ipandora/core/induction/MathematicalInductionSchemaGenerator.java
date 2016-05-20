package com.ipandora.core.induction;

import com.ipandora.api.predicate.formula.ForallFormula;
import com.ipandora.api.predicate.formula.Formula;
import com.ipandora.api.predicate.term.*;
import com.ipandora.api.predicate.term.Number;
import com.ipandora.core.formula.AtomicTermCollector;
import com.ipandora.core.formula.TermSubstitutor;
import com.ipandora.core.term.TermStringBuilder;

import java.util.*;

import static com.ipandora.core.util.CollectionUtils.extractMapValues;
import static com.ipandora.core.util.CollectionUtils.flatten;

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
    public InductionSchema generateSchema(ForallFormula forallFormula, Variable variable)
            throws SchemaGeneratorException {

        Map<Type, List<Variable>> allVariables = forallFormula.getVariablesByType();
        List<Variable> natVariables = allVariables.get(Type.NAT);
        if (variable.getType() != Type.NAT || natVariables == null || !natVariables.contains(variable)) {
            throw new SchemaGeneratorException("Cannot generate induction schema for variable of non-Nat type: " +
                    variable);
        }

        // Forall may be quantified over many variables. Remove the inductive variable...
        Map<Type, List<Variable>> newVariablesByType = getCopyWithNatVariableRemoved(allVariables, variable);

        Formula formula = forallFormula.getFormula();

        // Find all atoms in the remaining formula. This includes all those in the formula as well as remaining
        // variables introduced by forall...
        HashSet<Atom> remainingAtoms = flatten(extractMapValues(newVariablesByType), new HashSet<Atom>());
        remainingAtoms.addAll(atomicTermCollector.collectAtoms(formula));

        Formula baseCase = termSubstitutor.cloneAndSubstituteInScope(formula, variable, new Number(0));
        Constant k = getConstantWithNewName(remainingAtoms);
        Formula indHyp = termSubstitutor.cloneAndSubstituteInScope(formula, variable, k);
        Formula indCase = termSubstitutor.cloneAndSubstituteInScope(formula, variable, new Addition(k, new Number(1)));

        // If forall is quantified over many variables, each of the cases must be wrapped in forall quantifying
        // those which remain...
        if (!newVariablesByType.isEmpty()) {
            baseCase = new ForallFormula(newVariablesByType, baseCase);
            indHyp = new ForallFormula(newVariablesByType, indHyp);
            indCase = new ForallFormula(newVariablesByType, indCase);
        }

        return new InductionSchema(Collections.singletonList(baseCase), k, indHyp, Collections.singletonList(indCase));
    }

    private Map<Type, List<Variable>> getCopyWithNatVariableRemoved(Map<Type, List<Variable>> variablesByType,
                                                                    Variable natVariable) {

        Map<Type, List<Variable>> variablesByTypeCopy = new HashMap<>(variablesByType);
        List<Variable> natVariables = variablesByTypeCopy.get(Type.NAT);

        natVariables.remove(natVariable);
        if (natVariables.isEmpty()) {
            variablesByTypeCopy.remove(Type.NAT);
        }

        return variablesByTypeCopy;
    }

    private Constant getConstantWithNewName(Set<Atom> atoms) {
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

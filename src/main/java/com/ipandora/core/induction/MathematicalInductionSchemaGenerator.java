package com.ipandora.core.induction;

import com.ipandora.api.predicate.formula.ForallFormula;
import com.ipandora.api.predicate.formula.Formula;
import com.ipandora.api.predicate.term.*;
import com.ipandora.api.predicate.term.Number;
import com.ipandora.core.formula.TermVisitingFormulaVisitor;
import com.ipandora.core.formula.TermSubstitutor;
import com.ipandora.core.term.AtomCollectingTermVisitor;
import com.ipandora.core.term.TermStringBuilder;

import java.util.*;

import static com.ipandora.core.util.CollectionUtils.extractMapValues;
import static com.ipandora.core.util.CollectionUtils.flatten;

public class MathematicalInductionSchemaGenerator implements InductionSchemaGenerator {

    private static final String DEFAULT_INDUCTIVE_TERM_NAME = "k";
    private static final int SPECIAL_INDUCTIVE_TERM_NAME_INITIAL_SUFFIX = 1;

    private final TermSubstitutor termSubstitutor;
    private final TermStringBuilder termStringBuilder;

    public MathematicalInductionSchemaGenerator(TermStringBuilder termStringBuilder,
                                                TermSubstitutor termSubstitutor) {
        this.termStringBuilder = termStringBuilder;
        this.termSubstitutor = termSubstitutor;
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
        remainingAtoms.addAll(getAtomsFromFormula(formula));

        Formula baseCase = termSubstitutor.cloneAndSubstituteInScope(formula, variable, new Number(0));
        Variable k = getVariableWithNewName(remainingAtoms);
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

    private Set<Atom> getAtomsFromFormula(Formula formula) {
        AtomCollectingTermVisitor termVisitor = new AtomCollectingTermVisitor();
        TermVisitingFormulaVisitor formulaVisitor = new TermVisitingFormulaVisitor(termVisitor);
        formulaVisitor.visit(formula);

        Set<Atom> atoms = new HashSet<>();
        atoms.addAll(termVisitor.getVariables());
        atoms.addAll(termVisitor.getConstants());
        atoms.addAll(termVisitor.getFunctions());
        
        return atoms;
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

    private Variable getVariableWithNewName(Set<Atom> atoms) {
        // Try to use k by default
        String name = DEFAULT_INDUCTIVE_TERM_NAME;
        if (atomSetContainsAtomWithName(atoms, name)) {
            int suffix = SPECIAL_INDUCTIVE_TERM_NAME_INITIAL_SUFFIX;
            while (atomSetContainsAtomWithName(atoms, (name = String.format("k%d", suffix)))) {
                suffix++;
            }
        }

        return Variable.withTypeNat(name);
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

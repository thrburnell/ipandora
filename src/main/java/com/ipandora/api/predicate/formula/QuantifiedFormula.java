package com.ipandora.api.predicate.formula;

import com.ipandora.api.predicate.term.Type;
import com.ipandora.api.predicate.term.Variable;

import java.util.*;

import static com.ipandora.core.util.CollectionUtils.extractMapValues;
import static com.ipandora.core.util.CollectionUtils.flatten;

public abstract class QuantifiedFormula implements Formula {

    // Use a TreeMap so elements ordered by Type. UNKNOWN Type is the greatest, so always returned last.
    protected final TreeMap<Type, List<Variable>> variablesByType;
    protected final Formula formula;

    public QuantifiedFormula(Map<Type, List<Variable>> variablesByType, Formula formula) {
        this.variablesByType = new TreeMap<>(variablesByType);
        this.formula = formula;

    }

    public QuantifiedFormula(Variable variable, Formula formula) {
        this(formula, variable);
    }

    public QuantifiedFormula(Formula formula, Variable... variables) {
        if (variables.length == 0) {
            throw new IllegalArgumentException("Empty variable list given to quantified formula.");
        }

        this.variablesByType = new TreeMap<>();
        this.formula = formula;

        for (Variable variable : variables) {
            Type type = variable.getType();

            if (!variablesByType.containsKey(type)) {
                variablesByType.put(type, new ArrayList<Variable>());
            }

            variablesByType.get(type).add(variable);
        }
    }

    public Map<Type, List<Variable>> getVariablesByType() {
        return variablesByType;
    }

    public List<Variable> getVariables() {
        return flatten(extractMapValues(variablesByType), new ArrayList<Variable>());
    }

    public Formula getFormula() {
        return formula;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        QuantifiedFormula that = (QuantifiedFormula) o;

        if (!variablesByType.equals(that.variablesByType)) return false;
        return formula.equals(that.formula);
    }

    @Override
    public int hashCode() {
        int result = variablesByType.hashCode();
        result = 31 * result + formula.hashCode();
        return result;
    }
}

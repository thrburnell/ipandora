package com.ipandora.api.predicate.formula;

import com.ipandora.api.predicate.term.Variable;
import com.ipandora.core.formula.FormulaVisitor;

import java.util.List;

public class PredicateFormula implements Formula {

    private final String name;
    private final List<Variable> params;

    public PredicateFormula(String name, List<Variable> params) {
        this.name = name;
        this.params = params;
    }

    public String getName() {
        return name;
    }

    public List<Variable> getParams() {
        return params;
    }

    @Override
    public String toString() {

        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < params.size(); i++) {
            sb.append(params.get(i));
            if (i < params.size() - 1) {
                sb.append(", ");
            }
        }

        return String.format("%s(%s)", name, sb);
    }

    @Override
    public <T> T accept(FormulaVisitor<T> visitor) {
        return visitor.visitPredicateFormula(this);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        PredicateFormula that = (PredicateFormula) o;

        if (name != null ? !name.equals(that.name) : that.name != null) return false;
        return !(params != null ? !params.equals(that.params) : that.params != null);

    }

    @Override
    public int hashCode() {
        int result = name != null ? name.hashCode() : 0;
        result = 31 * result + (params != null ? params.hashCode() : 0);
        return result;
    }
}

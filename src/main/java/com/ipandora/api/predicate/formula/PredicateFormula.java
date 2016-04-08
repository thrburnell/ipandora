package com.ipandora.api.predicate.formula;

import com.ipandora.api.predicate.term.Term;
import com.ipandora.core.formula.FormulaVisitor;

import java.util.List;

public class PredicateFormula implements Formula {

    private final String name;
    private final List<Term> params;

    public PredicateFormula(String name, List<Term> params) {
        this.name = name;
        this.params = params;
    }

    public String getName() {
        return name;
    }

    public List<Term> getParams() {
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

}

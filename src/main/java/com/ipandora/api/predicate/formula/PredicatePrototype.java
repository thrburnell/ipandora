package com.ipandora.api.predicate.formula;

import com.ipandora.api.predicate.term.Term;
import com.ipandora.api.predicate.term.Type;

import java.util.ArrayList;
import java.util.List;

public class PredicatePrototype {

    private final String name;
    private final List<Type> argTypes;

    public PredicatePrototype(String name, List<Type> args) {
        this.name = name;
        this.argTypes = args;
    }

    public static PredicatePrototype fromPredicateFormula(PredicateFormula formula) {
        List<Term> params = formula.getParams();
        List<Type> types = new ArrayList<>(params.size());
        for (Term term : params) {
            types.add(term.getType());
        }

        return new PredicatePrototype(formula.getName(), types);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        PredicatePrototype that = (PredicatePrototype) o;

        if (!name.equals(that.name)) return false;
        return argTypes.equals(that.argTypes);
    }

    @Override
    public int hashCode() {
        int result = name.hashCode();
        result = 31 * result + argTypes.hashCode();
        return result;
    }

    public String getName() {
        return name;
    }

    public List<Type> getArgTypes() {
        return argTypes;
    }

}

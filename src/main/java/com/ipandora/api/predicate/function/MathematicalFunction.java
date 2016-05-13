package com.ipandora.api.predicate.function;

import com.ipandora.api.predicate.term.Variable;

import java.util.List;

public class MathematicalFunction implements Function {

    private final String name;
    private final List<Variable> arguments;
    private final List<FunctionCase> cases;

    public MathematicalFunction(String name, List<Variable> arguments, List<FunctionCase> cases) {
        this.name = name;
        this.arguments = arguments;
        this.cases = cases;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        MathematicalFunction that = (MathematicalFunction) o;

        if (!name.equals(that.name)) return false;
        if (!arguments.equals(that.arguments)) return false;
        return cases.equals(that.cases);
    }

    @Override
    public int hashCode() {
        int result = name.hashCode();
        result = 31 * result + arguments.hashCode();
        result = 31 * result + cases.hashCode();
        return result;
    }

}

package com.ipandora.api.predicate.function;

import com.ipandora.api.predicate.term.Variable;
import com.ipandora.core.function.FunctionDefinitionVisitor;

import java.util.List;

public class MathematicalFunctionDefinition implements FunctionDefinition {

    private final String name;
    private final List<Variable> arguments;
    private final List<FunctionCase> cases;

    public MathematicalFunctionDefinition(String name, List<Variable> arguments, List<FunctionCase> cases) {
        this.name = name;
        this.arguments = arguments;
        this.cases = cases;
    }

    public String getName() {
        return name;
    }

    public List<Variable> getArguments() {
        return arguments;
    }

    public List<FunctionCase> getCases() {
        return cases;
    }

    @Override
    public <T> T accept(FunctionDefinitionVisitor<T> visitor) {
        return visitor.visitMathematicalFunctionDefinition(this);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        MathematicalFunctionDefinition that = (MathematicalFunctionDefinition) o;

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

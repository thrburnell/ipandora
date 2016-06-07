package com.ipandora.api.predicate.function;

import com.ipandora.api.predicate.term.Type;
import com.ipandora.api.predicate.term.Variable;
import com.ipandora.core.function.FunctionDefinitionVisitor;

import java.util.List;

public class MathematicalFunctionDefinition implements FunctionDefinition {

    private final String name;
    private final List<Variable> arguments;
    private final List<FunctionCase> cases;
    private final Type returnType;

    public MathematicalFunctionDefinition(String name, List<Variable> arguments, List<FunctionCase> cases,
                                          Type returnType) {
        this.name = name;
        this.arguments = arguments;
        this.cases = cases;
        this.returnType = returnType;
    }

    @Override
    public String getName() {
        return name;
    }

    @Override
    public List<Variable> getArguments() {
        return arguments;
    }

    @Override
    public List<FunctionCase> getCases() {
        return cases;
    }

    @Override
    public Type getReturnType() {
        return returnType;
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
        if (!cases.equals(that.cases)) return false;
        return returnType == that.returnType;
    }

    @Override
    public int hashCode() {
        int result = name.hashCode();
        result = 31 * result + arguments.hashCode();
        result = 31 * result + cases.hashCode();
        result = 31 * result + returnType.hashCode();
        return result;
    }

}

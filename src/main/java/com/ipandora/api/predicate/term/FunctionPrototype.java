package com.ipandora.api.predicate.term;

import java.util.ArrayList;
import java.util.List;

public class FunctionPrototype {

    private final String name;
    private final List<Type> argTypes;
    private final Type returnType;

    public FunctionPrototype(String name, List<Type> argTypes, Type returnType) {
        this.name = name;
        this.argTypes = argTypes;
        this.returnType = returnType;
    }

    public static FunctionPrototype fromFunctionTerm(Function function) {

        List<Term> args = function.getArgs();
        List<Type> argTypes = new ArrayList<>(args.size());
        for (Term arg : args) {
            argTypes.add(arg.getType());
        }


        String name = function.getName();
        Type returnType = function.getType();

        return new FunctionPrototype(name, argTypes, returnType);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        FunctionPrototype that = (FunctionPrototype) o;

        if (!name.equals(that.name)) return false;
        if (!argTypes.equals(that.argTypes)) return false;
        return returnType == that.returnType;
    }

    @Override
    public int hashCode() {
        int result = name.hashCode();
        result = 31 * result + argTypes.hashCode();
        result = 31 * result + returnType.hashCode();
        return result;
    }

    public String getName() {
        return name;
    }

    public List<Type> getArgTypes() {
        return argTypes;
    }

    public Type getReturnType() {
        return returnType;
    }

}

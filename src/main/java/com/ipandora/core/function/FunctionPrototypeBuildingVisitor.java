package com.ipandora.core.function;

import com.ipandora.api.predicate.function.FunctionDefinition;
import com.ipandora.api.predicate.function.FunctionPrototype;
import com.ipandora.api.predicate.function.MathematicalFunctionDefinition;
import com.ipandora.api.predicate.term.Type;
import com.ipandora.api.predicate.term.Variable;

import java.util.ArrayList;
import java.util.List;

public class FunctionPrototypeBuildingVisitor implements FunctionDefinitionVisitor<FunctionPrototype> {

    @Override
    public FunctionPrototype visit(FunctionDefinition function) {
        return function.accept(this);
    }

    @Override
    public FunctionPrototype visitMathematicalFunctionDefinition(MathematicalFunctionDefinition mathematicalFunction) {
        String name = mathematicalFunction.getName();
        List<Variable> arguments = mathematicalFunction.getArguments();
        List<Type> types = new ArrayList<>();
        for (Variable arg : arguments) {
            types.add(arg.getType());
        }

        return new FunctionPrototype(name, types, Type.NAT);
    }

}

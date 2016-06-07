package com.ipandora.testutils;

import com.ipandora.api.predicate.formula.Formula;
import com.ipandora.api.predicate.function.FunctionCase;
import com.ipandora.api.predicate.function.MathematicalFunctionDefinition;
import com.ipandora.api.predicate.term.Term;
import com.ipandora.api.predicate.term.Variable;

import java.util.List;

public class FunctionCreators {

    public static MathematicalFunctionDefinition mathFun(String name, List<Variable> args, List<FunctionCase> cases) {
        return new MathematicalFunctionDefinition(name, args, cases);
    }

    public static FunctionCase funCase(Term expr, Formula cond) {
        return new FunctionCase(expr, cond);
    }

}

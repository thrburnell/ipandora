package com.ipandora.testutils;

import com.ipandora.api.predicate.formula.Formula;
import com.ipandora.api.predicate.function.*;
import com.ipandora.api.predicate.term.Term;
import com.ipandora.api.predicate.term.Variable;

import java.util.List;

public class FunctionCreators {

    public static MathematicalFunctionDefinition mathFun(String name, List<Variable> args, List<FunctionCase> cases) {
        return new MathematicalFunctionDefinition(name, args, cases);
    }

    public static FunctionCase funCase(Term expr, FunctionCaseCondition cond) {
        return new FunctionCase(expr, cond);
    }

    public static IfCondition ifCond(Formula form) {
        return new IfCondition(form);
    }

    public static OtherwiseCondition otherCond() {
        return new OtherwiseCondition();
    }

}

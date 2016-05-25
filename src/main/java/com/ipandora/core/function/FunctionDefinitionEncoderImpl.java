package com.ipandora.core.function;

import com.ipandora.api.predicate.formula.*;
import com.ipandora.api.predicate.function.FunctionCase;
import com.ipandora.api.predicate.function.FunctionDefinition;
import com.ipandora.api.predicate.function.MathematicalFunctionDefinition;
import com.ipandora.api.predicate.term.*;
import com.ipandora.api.predicate.term.Number;
import com.ipandora.core.formula.FormulaConjunctionReducer;

import java.util.ArrayList;
import java.util.List;

public class FunctionDefinitionEncoderImpl implements FunctionDefinitionEncoder {

    private final FormulaConjunctionReducer conjunctionReducer;

    public FunctionDefinitionEncoderImpl(FormulaConjunctionReducer conjunctionReducer) {
        this.conjunctionReducer = conjunctionReducer;
    }

    @Override
    public ForallFormula encode(FunctionDefinition definition) {
        return definition.accept(new FunctionDefinitionEncodingVisitor());
    }

    private class FunctionDefinitionEncodingVisitor implements FunctionDefinitionVisitor<ForallFormula> {

        @Override
        public ForallFormula visit(FunctionDefinition function) {
            return function.accept(this);
        }

        @Override
        public ForallFormula visitMathematicalFunctionDefinition(MathematicalFunctionDefinition mathematicalFunction) {

            String name = mathematicalFunction.getName();
            List<Variable> argVars = mathematicalFunction.getArguments();
            List<Term> args = termListFromVariableList(argVars);
            Function function = new Function(name, args, Type.NAT);

            List<Formula> formulas = new ArrayList<>();

            // Variable guards
            for (Variable argVar : argVars) {
                formulas.add(new GreaterThanEqualFormula(argVar, new Number(0)));
            }

            // Function cases
            for (FunctionCase functionCase : mathematicalFunction.getCases()) {
                Formula condition = functionCase.getCondition();
                Term expression =  functionCase.getExpression();
                ImpliesFormula formula = new ImpliesFormula(condition, new EqualToFormula(function, expression));
                formulas.add(formula);
            }

            Formula reduce = conjunctionReducer.reduce(formulas);
            return new ForallFormula(reduce, argVars.toArray(new Variable[argVars.size()]));
        }

        private List<Term> termListFromVariableList(List<Variable> variables) {
            List<Term> terms = new ArrayList<>();

            for (Variable variable : variables) {
                terms.add(variable);
            }

            return terms;
        }


    }

}

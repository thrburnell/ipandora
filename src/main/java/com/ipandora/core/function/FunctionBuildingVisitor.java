package com.ipandora.core.function;

import com.ipandora.api.predicate.formula.Formula;
import com.ipandora.api.predicate.formula.NotFormula;
import com.ipandora.api.predicate.formula.TruthFormula;
import com.ipandora.api.predicate.function.FunctionCase;
import com.ipandora.api.predicate.function.FunctionDefinition;
import com.ipandora.api.predicate.function.FunctionPrototype;
import com.ipandora.api.predicate.function.MathematicalFunctionDefinition;
import com.ipandora.api.predicate.term.Term;
import com.ipandora.api.predicate.term.Type;
import com.ipandora.api.predicate.term.Variable;
import com.ipandora.core.formula.FormulaBuildingVisitor;
import com.ipandora.core.formula.FormulaConjunctionReducer;
import com.ipandora.core.term.TermBuildingVisitor;
import com.ipandora.parser.PredicateLogicBaseVisitor;
import com.ipandora.parser.PredicateLogicParser;
import org.antlr.v4.runtime.Token;

import java.util.ArrayList;
import java.util.List;

public class FunctionBuildingVisitor extends PredicateLogicBaseVisitor<FunctionDefinition> {

    private final FormulaBuildingVisitor formulaBuildingVisitor;
    private final TermBuildingVisitor termBuildingVisitor;
    private final FormulaConjunctionReducer conjunctionReducer;

    public FunctionBuildingVisitor(FormulaBuildingVisitor formulaBuildingVisitor,
                                   TermBuildingVisitor termBuildingVisitor,
                                   FormulaConjunctionReducer conjunctionReducer) {
        this.formulaBuildingVisitor = formulaBuildingVisitor;
        this.termBuildingVisitor = termBuildingVisitor;
        this.conjunctionReducer = conjunctionReducer;
    }

    @Override
    public FunctionDefinition visitFunctionDefinition(PredicateLogicParser.FunctionDefinitionContext ctx) {
        String name = ctx.name.getText();
        List<Variable> variables = createVariables(ctx.args.args);

        // Add typing for all arguments before building the cases:
        List<Type> argTypes = new ArrayList<>();
        for (Variable variable : variables) {
            Type type = variable.getType();
            termBuildingVisitor.addTypeMapping(variable.getName(), type);
            argTypes.add(type);
        }

        // Assume functions always return Nat
        FunctionPrototype prototype = new FunctionPrototype(name, argTypes, Type.NAT);
        termBuildingVisitor.addFunctionPrototypeMapping(name, prototype);

        List<FunctionCase> cases = createCases(ctx.cases);
        return new MathematicalFunctionDefinition(name, variables, cases);
    }

    private List<Variable> createVariables(List<Token> argTokens) {

        if (argTokens.isEmpty()) {
            throw new IllegalFunctionException("No arguments given with function definition.");
        }

        ArrayList<Variable> variables = new ArrayList<>();

        for (Token argToken : argTokens) {
            variables.add(Variable.withTypeNat(argToken.getText()));
        }

        return variables;
    }

    private List<FunctionCase> createCases(List<PredicateLogicParser.FnCaseContext> fnCaseContexts) {

        if (fnCaseContexts.isEmpty()) {
            throw new IllegalFunctionException("No cases given with function definition.");
        }

        ArrayList<FunctionCase> functionCases = new ArrayList<>();

        List<Formula> negatedPreviousConditions = new ArrayList<>();
        for (PredicateLogicParser.FnCaseContext fnCaseContext : fnCaseContexts) {

            Term expression = termBuildingVisitor.visit(fnCaseContext.expr);
            Formula condition;

            PredicateLogicParser.FormulaContext condCtx = fnCaseContext.cond;
            if (condCtx == null) {
                condition = negatedPreviousConditions.isEmpty() ?
                        new TruthFormula() : conjunctionReducer.reduce(negatedPreviousConditions);
            } else {
                condition = formulaBuildingVisitor.visit(condCtx);
                negatedPreviousConditions.add(new NotFormula(condition));
            }

            functionCases.add(new FunctionCase(expression, condition));
        }

        return functionCases;
    }

}

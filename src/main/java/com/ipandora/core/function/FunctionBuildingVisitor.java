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
import com.ipandora.core.formula.InvalidSyntaxException;
import com.ipandora.core.term.TermBuildingVisitor;
import com.ipandora.core.util.WrappingRuntimeException;
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

        PredicateLogicParser.FunctionPrototypeContext proto = ctx.proto;
        FunctionPrototype prototype = makePrototype(proto);
        PredicateLogicParser.DefinitionContext def = ctx.def;

        String name = def.name.getText();
        if (!name.equals(proto.name.getText())) {
            throw new WrappingRuntimeException(
                    new IllegalFunctionException("Name of function in prototype doesn't match name in definition."));
        }

        List<String> argNames = new ArrayList<>();
        for (PredicateLogicParser.AnyNameContext arg : def.args.args) {
            argNames.add(arg.getText());
        }

        List<Variable> variables = makeVariables(argNames, prototype.getArgTypes());

        // Add typing for all arguments before building the cases:
        for (Variable variable : variables) {
            termBuildingVisitor.addTypeMapping(variable.getName(), variable.getType());
        }

        termBuildingVisitor.addFunctionPrototypeMapping(name, prototype);
        List<FunctionCase> functionCases = makeCases(def.cases);

        return new MathematicalFunctionDefinition(name, variables, functionCases, prototype.getReturnType());
    }

    private FunctionPrototype makePrototype(PredicateLogicParser.FunctionPrototypeContext ctx) {

        String name = ctx.name.getText();

        List<Token> types = ctx.types.types;

        if (types.isEmpty()) {
            throw new WrappingRuntimeException(
                    new IllegalFunctionException("No return type given for function definition"));
        }

        ArrayList<Type> argTypes = new ArrayList<>();
        for (int i = 0; i < types.size() - 1; i++) {
            Type argType = Type.withIdentifier(types.get(i).getText());
            argTypes.add(argType);
        }

        Type returnType = Type.withIdentifier(types.get(types.size() - 1).getText());

        return new FunctionPrototype(name, argTypes, returnType);
    }

    private List<Variable> makeVariables(List<String> argNames, List<Type> argTypes) {

        if (argNames.isEmpty()) {
            throw new WrappingRuntimeException(
                    new IllegalFunctionException("No arguments given with function definition."));
        }

        if (argNames.size() != argTypes.size()) {
            throw new WrappingRuntimeException(
                    new IllegalFunctionException("Different number of args given in prototype and definition."));
        }

        ArrayList<Variable> variables = new ArrayList<>();

        for (int i = 0; i < argNames.size(); i++) {
            variables.add(new Variable(argNames.get(i), argTypes.get(i)));
        }

        return variables;
    }

    private List<FunctionCase> makeCases(PredicateLogicParser.FnCasesContext fnCasesContext) {

        ArrayList<FunctionCase> functionCases = new ArrayList<>();
        List<Formula> negatedPreviousConditions = new ArrayList<>();

        while (fnCasesContext != null) {
            Term expression;
            Formula condition;

            if (fnCasesContext.ifFnCase != null) {

                PredicateLogicParser.IfCaseContext ifFnCase = fnCasesContext.ifFnCase;
                expression = termBuildingVisitor.visit(ifFnCase.expr);
                condition = formulaBuildingVisitor.visit(ifFnCase.cond);
                negatedPreviousConditions.add(new NotFormula(condition));

            } else if (fnCasesContext.otherwiseFnCase != null) {

                expression = termBuildingVisitor.visit(fnCasesContext.otherwiseFnCase.expr);
                condition = negatedPreviousConditions.isEmpty() ?
                        new TruthFormula() : conjunctionReducer.reduce(negatedPreviousConditions);

            } else {
                throw new WrappingRuntimeException(
                        new InvalidSyntaxException("Function case contained no if or otherwise case."));
            }

            functionCases.add(new FunctionCase(expression, condition));
            fnCasesContext = fnCasesContext.rest;
        }

        return functionCases;
    }

}

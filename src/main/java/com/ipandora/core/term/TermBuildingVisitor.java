package com.ipandora.core.term;

import com.ipandora.api.predicate.term.*;
import com.ipandora.api.predicate.term.Number;
import com.ipandora.core.formula.InvalidSyntaxException;
import com.ipandora.core.util.Creator;
import com.ipandora.core.util.WrappingRuntimeException;
import com.ipandora.parser.*;
import org.antlr.v4.runtime.Token;

import java.util.ArrayList;
import java.util.List;

public class TermBuildingVisitor extends PredicateLogicBaseVisitor<Term> {

    private final Creator<SymbolTable> symbolTableCreator;
    private SymbolTable symbolTable;

    public TermBuildingVisitor(Creator<SymbolTable> symbolTableCreator) {
        this.symbolTableCreator = symbolTableCreator;
        this.symbolTable = symbolTableCreator.create();
    }

    @Override
    public Term visitMathExprOnly(PredicateLogicParser.MathExprOnlyContext ctx) {
        return visit(ctx.expr);
    }

    @Override
    public Term visitMathExpr(PredicateLogicParser.MathExprContext ctx) {

        PredicateLogicParser.SumExprContext term = ctx.term;
        if (term != null) {
            return visit(term);
        }

        Term left = visit(ctx.lhs);
        Term right = visit(ctx.rhs);

        switch (ctx.op.getType()) {
            case PredicateLogicLexer.PLUS:
                return new Addition(left, right);
            case PredicateLogicLexer.MINUS:
                return new Subtraction(left, right);
        }

        throw new WrappingRuntimeException(
                new InvalidSyntaxException("Unknown mathematical operator " + ctx.op.getText()));
    }

    @Override
    public Term visitSumExpr(PredicateLogicParser.SumExprContext ctx) {

        PredicateLogicParser.MathTermContext term = ctx.term;
        if (term != null) {
            return visit(term);
        }

        // Variable bound by summation is the index, so always has type Nat
        String varName = ctx.var.getText();
        Variable var = new Variable(varName, Type.NAT);
        Term lower = visit(ctx.lower);
        Term upper = visit(ctx.upper);

        // Sum is a function, so introduces a new scope for its summing element
        enterNewScope();
        addTypeMapping(varName, Type.NAT);
        Term elem = visit(ctx.elem);
        exitScope();

        return new Summation(var, lower, upper, elem);
    }

    @Override
    public Term visitMathTerm(PredicateLogicParser.MathTermContext ctx) {

        PredicateLogicParser.PowerTermContext term = ctx.term;
        if (term != null) {
            return visit(term);
        }

        Term left = visit(ctx.lhs);
        Term right = visit(ctx.rhs);

        switch (ctx.op.getType()) {
            case PredicateLogicLexer.MULTIPLY:
                return new Multiplication(left, right);
            case PredicateLogicLexer.DIVIDE:
                return new Division(left, right);
        }

        throw new WrappingRuntimeException(
                new InvalidSyntaxException("Unknown mathematical operator " + ctx.op.getText()));
    }

    @Override
    public Term visitPowerTerm(PredicateLogicParser.PowerTermContext ctx) {

        PredicateLogicParser.LeafTermContext term = ctx.term;
        if (term != null) {
            return visit(term);
        }

        PredicateLogicParser.PowerTermContext base = ctx.base;
        Token exponentTok = ctx.exponent;

        int exponent = Integer.parseInt(exponentTok.getText());
        return new Power(visit(base), exponent);
    }

    @Override
    public Term visitLeafTerm(PredicateLogicParser.LeafTermContext ctx) {

        Token term = ctx.term;
        if (term != null) {
            String name = term.getText();
            Type type = symbolTable.getType(name);
            return type == null ? new Constant(name) : new Variable(name, type);
        }

        Token number = ctx.number;
        if (number != null) {
            String numberString = number.getText();
            int numberInt = Integer.parseInt(numberString);
            return new Number(numberInt);
        }

        PredicateLogicParser.MathExprContext expr = ctx.expr;
        if (expr != null) {
            return visit(expr);
        }

        PredicateLogicParser.FunctionContext func = ctx.func;
        if (func != null) {
            return visit(func);
        }

        throw new WrappingRuntimeException(
                new InvalidSyntaxException("Leaf term contained no var, constant, number, expr or func"));
    }

    @Override
    public Term visitFunction(PredicateLogicParser.FunctionContext ctx) {

        String name = ctx.name.getText();

        List<Term> args = new ArrayList<>();
        for (PredicateLogicParser.MathExprContext arg : ctx.args.args) {
            args.add(visit(arg));
        }

        return new Function(name, args);
    }

    public void enterNewScope() {
        SymbolTable childTable = symbolTableCreator.create();
        childTable.setParent(symbolTable);
        symbolTable = childTable;
    }

    public void exitScope() {
        symbolTable = symbolTable.getParent();
    }

    public void addTypeMapping(String variableName, Type type) {
        symbolTable.addMapping(variableName, type);
    }
}

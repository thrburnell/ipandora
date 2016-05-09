package com.ipandora.core.term;

import com.ipandora.api.predicate.term.*;
import com.ipandora.api.predicate.term.Number;
import com.ipandora.parser.PredicateLogicBaseVisitor;
import com.ipandora.parser.PredicateLogicLexer;
import com.ipandora.parser.PredicateLogicParser;
import org.antlr.v4.runtime.Token;

import java.util.ArrayList;
import java.util.List;

public class TermBuildingVisitor extends PredicateLogicBaseVisitor<Term> {

    @Override
    public Term visitMathExpr(PredicateLogicParser.MathExprContext ctx) {

        PredicateLogicParser.SumExprContext term = ctx.term;
        if (term != null) {
            return visit(term);
        }

        Term left = visit(ctx.lhs);
        Term right = visit(ctx.rhs);

        if (ctx.op.getType() == PredicateLogicLexer.PLUS) {
            return new Addition(left, right);
        } else {
            return new Subtraction(left, right);
        }
    }

    @Override
    public Term visitSumExpr(PredicateLogicParser.SumExprContext ctx) {

        PredicateLogicParser.MathTermContext term = ctx.term;
        if (term != null) {
            return visit(term);
        }

        Variable var = new Variable(ctx.var.getText());
        Term lower = visit(ctx.lower);
        Term upper = visit(ctx.upper);
        Term elem = visit(ctx.elem);

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

        if (ctx.op.getType() == PredicateLogicLexer.MULTIPLY) {
            return new Multiplication(left, right);
        } else {
            return new Division(left, right);
        }
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
        Token var = ctx.var;
        if (var != null) {
            return new Variable(var.getText());
        }

        Token constant = ctx.constant;
        if (constant != null) {
            return new Constant(constant.getText());
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
        return visit(func);
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
    
}

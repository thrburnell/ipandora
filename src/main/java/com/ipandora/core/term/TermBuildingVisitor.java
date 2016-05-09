package com.ipandora.core.term;

import com.ipandora.api.predicate.term.*;
import com.ipandora.parser.PredicateLogicBaseVisitor;
import com.ipandora.parser.PredicateLogicLexer;
import com.ipandora.parser.PredicateLogicParser;
import org.antlr.v4.runtime.Token;

public class TermBuildingVisitor extends PredicateLogicBaseVisitor<Term> {

    @Override
    public Term visitMathExpr(PredicateLogicParser.MathExprContext ctx) {

        PredicateLogicParser.MathTermContext term = ctx.term;
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
    public Term visitMathTerm(PredicateLogicParser.MathTermContext ctx) {

        PredicateLogicParser.LeafTermContext term = ctx.term;
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
    public Term visitLeafTerm(PredicateLogicParser.LeafTermContext ctx) {
        Token var = ctx.var;
        if (var != null) {
            return new Variable(var.getText());
        }

        Token constant = ctx.constant;
        if (constant != null) {
            return new Constant(constant.getText());
        }

        PredicateLogicParser.MathExprContext expr = ctx.expr;
        return visit(expr);
    }
    
}

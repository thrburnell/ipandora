package com.ipandora.core.formula;

import com.ipandora.api.predicate.formula.*;
import com.ipandora.api.predicate.term.Term;
import com.ipandora.api.predicate.term.Type;
import com.ipandora.api.predicate.term.Variable;
import com.ipandora.core.term.TermBuildingVisitor;
import com.ipandora.parser.PredicateLogicBaseVisitor;
import com.ipandora.parser.PredicateLogicLexer;
import com.ipandora.parser.PredicateLogicParser;

import java.util.ArrayList;
import java.util.List;

public class FormulaBuildingVisitor extends PredicateLogicBaseVisitor<Formula> {

    private final TermBuildingVisitor termBuildingVisitor;

    public FormulaBuildingVisitor(TermBuildingVisitor termBuildingVisitor) {
        this.termBuildingVisitor = termBuildingVisitor;
    }

    @Override
    public Formula visitFormula(PredicateLogicParser.FormulaContext ctx) {

        PredicateLogicParser.IffElementContext lhs = ctx.lhs;
        PredicateLogicParser.FormulaContext rhs = ctx.rhs;

        Formula lhsFormula = visit(lhs);

        if (rhs == null) {
            return lhsFormula;
        }

        Formula rhsFormula = visit(rhs);
        return new IffFormula(lhsFormula, rhsFormula);
    }

    @Override
    public Formula visitIffElement(PredicateLogicParser.IffElementContext ctx) {

        PredicateLogicParser.ImpliesElementContext lhs = ctx.lhs;
        PredicateLogicParser.IffElementContext rhs = ctx.rhs;

        Formula lhsFormula = visit(lhs);

        if (rhs == null) {
            return lhsFormula;
        }

        Formula rhsFormula = visit(rhs);
        return new ImpliesFormula(lhsFormula, rhsFormula);
    }

    @Override
    public Formula visitImpliesElement(PredicateLogicParser.ImpliesElementContext ctx) {

        PredicateLogicParser.ConjunctionContext lhs = ctx.lhs;
        PredicateLogicParser.ImpliesElementContext rhs = ctx.rhs;

        Formula lhsFormula = visit(lhs);

        if (rhs == null) {
            return lhsFormula;
        }

        Formula rhsFormula = visit(rhs);
        return new OrFormula(lhsFormula, rhsFormula);
    }

    @Override
    public Formula visitConjunction(PredicateLogicParser.ConjunctionContext ctx) {

        PredicateLogicParser.NegElementContext lhs = ctx.lhs;
        PredicateLogicParser.ConjunctionContext rhs = ctx.rhs;

        Formula lhsFormula = visit(lhs);

        if (rhs == null) {
            return lhsFormula;
        }


        Formula rhsFormula = visit(rhs);
        return new AndFormula(lhsFormula, rhsFormula);
    }

    @Override
    public Formula visitNegElement(PredicateLogicParser.NegElementContext ctx) {

        Formula formula = visit(ctx.elem);

        if (ctx.not != null) {
            return new NotFormula(formula);
        }

        return formula;
    }

    @Override
    public Formula visitElement(PredicateLogicParser.ElementContext ctx) {

        if (ctx.quant != null) {
            return visit(ctx.quant);
        }

        if (ctx.pred != null) {
            return visit(ctx.pred);
        }

        if (ctx.expr != null) {
            return visit(ctx.expr);
        }

        if (ctx.form != null) {
            return visit(ctx.form);
        }

        if (ctx.tf != null) {
            switch (ctx.tf.getType()) {
                case PredicateLogicLexer.TRUTH:
                    return new TruthFormula();
                case PredicateLogicLexer.FALSITY:
                    return new FalsityFormula();
            }

            throw new IllegalFormulaException("Unknown truth/falsity value: " + ctx.tf.getText());
        }

        throw new IllegalFormulaException("Element contained no quant, pred, expr or form: " + ctx);
    }

    @Override
    public Formula visitQuantified(PredicateLogicParser.QuantifiedContext ctx) {

        Type type = getTypeFromDomain(ctx.dom);
        String variableName = ctx.var.getText();
        Variable variable = new Variable(variableName, type);

        termBuildingVisitor.enterNewScope();
        termBuildingVisitor.addTypeMapping(variableName, type);
        Formula formula = visit(ctx.elem);
        termBuildingVisitor.exitScope();

        switch (ctx.quant.getType()) {
            case PredicateLogicLexer.FORALL:
                return new ForallFormula(variable, formula);
            case PredicateLogicLexer.EXISTS:
                return new ExistsFormula(variable, formula);
        }

        throw new IllegalFormulaException("Unknown quantifier " + ctx.quant.getText());
    }

    @Override
    public Formula visitPredicate(PredicateLogicParser.PredicateContext ctx) {

        String name = ctx.name.getText();

        PredicateLogicParser.ArgListContext argList = ctx.args;

        if (argList == null) {
            return new PropositionFormula(name);
        }

        List<Term> params = new ArrayList<>();
        for (PredicateLogicParser.MathExprContext arg : argList.args) {
            params.add(termBuildingVisitor.visit(arg));
        }

        return new PredicateFormula(name, params);
    }

    @Override
    public Formula visitBoolExpr(PredicateLogicParser.BoolExprContext ctx) {

        Term lhs = termBuildingVisitor.visit(ctx.lhs);
        Term rhs = termBuildingVisitor.visit(ctx.rhs);

        switch (ctx.op.getType()) {
            case PredicateLogicLexer.ET:
                return new EqualToFormula(lhs, rhs);
            case PredicateLogicLexer.GT:
                return new GreaterThanFormula(lhs, rhs);
            case PredicateLogicLexer.LT:
                return new LessThanFormula(lhs, rhs);
            case PredicateLogicLexer.GTE:
                return new GreaterThanEqualFormula(lhs, rhs);
            case PredicateLogicLexer.LTE:
                return new LessThanEqualFormula(lhs, rhs);
        }

        throw new IllegalFormulaException("Unknown boolean operator " + ctx.op.getText());
    }

    private Type getTypeFromDomain(PredicateLogicParser.DomainContext ctx) {

        if (ctx == null) {
            return Type.UNKNOWN;
        }

        switch (ctx.type.getType()) {
            case PredicateLogicLexer.NAT: return Type.NAT;
        }

        throw new IllegalFormulaException("Unknown type " + ctx.type.getText());
    }

}

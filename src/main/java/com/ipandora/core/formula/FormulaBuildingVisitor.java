package com.ipandora.core.formula;

import com.ipandora.api.predicate.formula.*;
import com.ipandora.api.predicate.term.Variable;
import com.ipandora.parser.PredicateLogicBaseVisitor;
import com.ipandora.parser.PredicateLogicLexer;
import com.ipandora.parser.PredicateLogicParser;
import org.antlr.v4.runtime.Token;

import java.util.ArrayList;
import java.util.List;

public class FormulaBuildingVisitor extends PredicateLogicBaseVisitor<Formula> {

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

        // An element is either quant, pred or form
        return visit(ctx.form);
    }

    @Override
    public Formula visitQuantified(PredicateLogicParser.QuantifiedContext ctx) {

        String variableName = ctx.var.getText();
        Variable variable = new Variable(variableName);

        Formula formula = visit(ctx.elem);

        if (ctx.quant.getType() == PredicateLogicLexer.FORALL) {
            return new ForallFormula(variable, formula);
        } else {
            return new ExistsFormula(variable, formula);
        }
    }

    @Override
    public Formula visitPredicate(PredicateLogicParser.PredicateContext ctx) {

        String name = ctx.name.getText();

        PredicateLogicParser.ArgListContext argList = ctx.args;

        if (argList == null) {
            return new PropositionFormula(name);
        }

        List<Variable> params = new ArrayList<>();
        for (PredicateLogicParser.ArgContext arg : argList.args) {
            params.add(generateVariable(arg));
        }

        return new PredicateFormula(name, params);
    }

    private Variable generateVariable(PredicateLogicParser.ArgContext ctx) {
        Token var = ctx.var;
        return new Variable(var.getText());
    }

}

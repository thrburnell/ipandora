package com.ipandora.core.formula;

import com.ipandora.api.predicate.formula.*;
import com.ipandora.api.predicate.term.Term;
import com.ipandora.core.term.TermStringBuilder;
import com.ipandora.core.util.PrettyStringBuilder;
import org.apache.commons.lang3.StringUtils;

import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

public class FormulaStringBuilder implements PrettyStringBuilder<Formula>, FormulaVisitor<String> {

    private final Stack<LogicConnective> connectiveStack = new Stack<>();
    private final TermStringBuilder termStringBuilder;

    public FormulaStringBuilder(TermStringBuilder termStringBuilder) {
        this.termStringBuilder = termStringBuilder;
    }

    @Override
    public String build(Formula formula) {
        return visit(formula);
    }

    @Override
    public String visit(Formula formula) {
        return formula.accept(this);
    }

    @Override
    public String visitAndFormula(AndFormula andFormula) {
        LogicConnective and = LogicConnective.AND;

        connectiveStack.push(and);
        String left = visit(andFormula.getLeft());
        String right = visit(andFormula.getRight());
        connectiveStack.pop();

        String result = String.format("%s & %s", left, right);

        if (doesCurrentContextBindStronger(and)) {
            result = wrapInParenthesis(result);
        }

        return result;
    }

    @Override
    public String visitOrFormula(OrFormula orFormula) {
        LogicConnective or = LogicConnective.OR;
        connectiveStack.push(or);
        String left = visit(orFormula.getLeft());
        String right = visit(orFormula.getRight());
        connectiveStack.pop();

        String result = String.format("%s | %s", left, right);

        if (doesCurrentContextBindStronger(or)) {
            result = wrapInParenthesis(result);
        }

        return result;
    }

    @Override
    public String visitForallFormula(ForallFormula forallFormula) {
        LogicConnective forall = LogicConnective.FORALL;
        connectiveStack.push(forall);
        String variable = termStringBuilder.build(forallFormula.getVariable());
        String formula = visit(forallFormula.getFormula());
        connectiveStack.pop();

        String result = String.format("\\FORALL %s %s", variable, formula);

        if (doesCurrentContextBindStronger(forall)) {
            result = wrapInParenthesis(result);
        }

        return result;
    }

    @Override
    public String visitExistsFormula(ExistsFormula existsFormula) {
        LogicConnective exists = LogicConnective.EXISTS;
        connectiveStack.push(exists);
        String variable = termStringBuilder.build(existsFormula.getVariable());
        String formula = visit(existsFormula.getFormula());
        connectiveStack.pop();

        String result = String.format("\\EXISTS %s %s", variable, formula);

        if (doesCurrentContextBindStronger(exists)) {
            result = wrapInParenthesis(result);
        }

        return result;
    }

    @Override
    public String visitTruthFormula(TruthFormula truthFormula) {
        return "\\TRUTH";
    }

    @Override
    public String visitFalsityFormula(FalsityFormula falsityFormula) {
        return "\\FALSITY";
    }

    @Override
    public String visitImpliesFormula(ImpliesFormula impliesFormula) {
        LogicConnective implies = LogicConnective.IMPLIES;
        connectiveStack.push(implies);
        String left = visit(impliesFormula.getLeft());
        String right = visit(impliesFormula.getRight());
        connectiveStack.pop();

        String result = String.format("%s -> %s", left, right);

        if (doesCurrentContextBindStrongerOrEqual(implies)) {
            result = wrapInParenthesis(result);
        }

        return result;
    }

    @Override
    public String visitIffFormula(IffFormula iffFormula) {
        LogicConnective iff = LogicConnective.IFF;
        connectiveStack.push(iff);
        String left = visit(iffFormula.getLeft());
        String right = visit(iffFormula.getRight());
        connectiveStack.pop();

        String result = String.format("%s <-> %s", left, right);

        if (doesCurrentContextBindStrongerOrEqual(iff)) {
            result = wrapInParenthesis(result);
        }

        return result;
    }

    @Override
    public String visitNotFormula(NotFormula notFormula) {
        LogicConnective not = LogicConnective.NOT;
        connectiveStack.push(not);
        String result = String.format("!%s", visit(notFormula.getFormula()));
        connectiveStack.pop();

        if (doesCurrentContextBindStronger(not)) {
            result = wrapInParenthesis(result);
        }

        return result;
    }

    @Override
    public String visitPropositionFormula(PropositionFormula propositionFormula) {
        return propositionFormula.getName();
    }

    @Override
    public String visitPredicateFormula(PredicateFormula predicateFormula) {
        String name = predicateFormula.getName();

        List<String> paramStrings = new ArrayList<>();
        for (Term param : predicateFormula.getParams()) {
            paramStrings.add(termStringBuilder.build(param));
        }

        String params = StringUtils.join(paramStrings, ", ");

        return String.format("%s(%s)", name, params);
    }

    @Override
    public String visitEqualToFormula(EqualToFormula equalToFormula) {
        String left = termStringBuilder.build(equalToFormula.getLeft());
        String right = termStringBuilder.build(equalToFormula.getRight());
        return String.format("(%s = %s)", left, right);
    }

    @Override
    public String visitGreaterThanFormula(GreaterThanFormula greaterThanFormula) {
        String left = termStringBuilder.build(greaterThanFormula.getLeft());
        String right = termStringBuilder.build(greaterThanFormula.getRight());
        return String.format("(%s > %s)", left, right);
    }

    @Override
    public String visitLessThanFormula(LessThanFormula lessThanFormula) {
        String left = termStringBuilder.build(lessThanFormula.getLeft());
        String right = termStringBuilder.build(lessThanFormula.getRight());
        return String.format("(%s < %s)", left, right);
    }

    @Override
    public String visitGreaterThanEqualFormula(GreaterThanEqualFormula greaterThanEqualFormula) {
        String left = termStringBuilder.build(greaterThanEqualFormula.getLeft());
        String right = termStringBuilder.build(greaterThanEqualFormula.getRight());
        return String.format("(%s >= %s)", left, right);
    }

    @Override
    public String visitLessThanEqualFormula(LessThanEqualFormula lessThanEqualFormula) {
        String left = termStringBuilder.build(lessThanEqualFormula.getLeft());
        String right = termStringBuilder.build(lessThanEqualFormula.getRight());
        return String.format("(%s <= %s)", left, right);
    }

    private boolean doesCurrentContextBindStronger(LogicConnective connective) {
        return !connectiveStack.isEmpty() && connectiveStack.peek().getPrecedence() > connective.getPrecedence();
    }

    private boolean doesCurrentContextBindStrongerOrEqual(LogicConnective connective) {
        return !connectiveStack.isEmpty() && connectiveStack.peek().getPrecedence() >= connective.getPrecedence();
    }

    private String wrapInParenthesis(String result) {
        return String.format("(%s)", result);
    }

}

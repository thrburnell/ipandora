package com.ipandora.core.z3;

import com.ipandora.api.predicate.formula.*;
import com.ipandora.api.predicate.term.Variable;
import com.ipandora.core.formula.FormulaVisitor;
import org.apache.commons.lang3.StringUtils;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class SMTGeneratingFormulaVisitor implements FormulaVisitor<String> {

    private static final String TYPE_NAME = "Type";

    private Map<String, Integer> predicates = new HashMap<>();

    public String getPredicateDefinitions() {
        StringBuilder sb = new StringBuilder();

        for (Map.Entry<String, Integer> predicate : predicates.entrySet()) {
            String params = StringUtils.repeat(TYPE_NAME, " ", predicate.getValue());
            sb.append(String.format("(declare-fun %s (%s) Bool)\n", predicate.getKey(), params));
        }

        return sb.toString();
    }

    public String getTypeDefinition() {
        return predicates.isEmpty() ? "" : "(declare-sort Type)";
    }

    @Override
    public String visit(Formula formula) {
        return formula.accept(this);
    }

    @Override
    public String visitAndFormula(AndFormula andFormula) {
        Formula left = andFormula.getLeft();
        Formula right = andFormula.getRight();
        return "(and " + visit(left) + " " + visit(right) + ")";
    }

    @Override
    public String visitOrFormula(OrFormula orFormula) {
        Formula left = orFormula.getLeft();
        Formula right = orFormula.getRight();
        return "(or " + visit(left) + " " + visit(right) + ")";
    }

    @Override
    public String visitForallFormula(ForallFormula forallFormula) {
        String variableName = forallFormula.getVariable().getName();
        Formula formula = forallFormula.getFormula();

        return "(forall ((" + variableName + " " + TYPE_NAME + ")) " + visit(formula) + ")";
    }

    @Override
    public String visitExistsFormula(ExistsFormula existsFormula) {

        // Z3 only supports forall. Use equivalence (exists x. foo) === (!(forall x. !foo))

        Variable variable = existsFormula.getVariable();
        Formula formula = existsFormula.getFormula();

        NotFormula equivalent = new NotFormula(new ForallFormula(variable, new NotFormula(formula)));

        return visit(equivalent);
    }

    @Override
    public String visitTrueFormula(TrueFormula trueFormula) {
        return "true";
    }

    @Override
    public String visitFalseFormula(FalseFormula falseFormula) {
        return "false";
    }

    @Override
    public String visitImpliesFormula(ImpliesFormula impliesFormula) {
        Formula left = impliesFormula.getLeft();
        Formula right = impliesFormula.getRight();
        return "(=> " + visit(left) + " " + visit(right) + ")";
    }

    @Override
    public String visitIffFormula(IffFormula iffFormula) {
        Formula left = iffFormula.getLeft();
        Formula right = iffFormula.getRight();
        return "(= " + visit(left) + " " + visit(right) + ")";
    }

    @Override
    public String visitNotFormula(NotFormula notFormula) {
        Formula formula = notFormula.getFormula();
        return "(not " + visit(formula) + ")";
    }

    @Override
    public String visitPredicateFormula(PredicateFormula predicateFormula) {
        String name = predicateFormula.getName();
        List<Variable> params = predicateFormula.getParams();

        predicates.put(name, params.size());

        String paramsString = getSpaceDelimitedVariableNames(params);
        return "(" + name + " " + paramsString + ")";
    }

    private String getSpaceDelimitedVariableNames(List<Variable> params) {
        StringBuilder paramsString = new StringBuilder(params.get(0).getName());

        for (int i = 1; i < params.size(); i++) {
            paramsString.append(" ").append(params.get(i).getName());
        }

        return paramsString.toString();
    }

}

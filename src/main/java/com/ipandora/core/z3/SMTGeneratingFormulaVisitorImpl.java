package com.ipandora.core.z3;

import com.ipandora.api.predicate.formula.*;
import com.ipandora.api.predicate.term.Term;
import com.ipandora.api.predicate.term.Type;
import com.ipandora.api.predicate.term.Variable;
import org.apache.commons.lang3.StringUtils;

import java.util.*;

public class SMTGeneratingFormulaVisitorImpl implements SMTGeneratingFormulaVisitor {

    private static final String TYPE_NAME = "Type";

    private final Map<String, Integer> predicates = new HashMap<>();
    private final Set<String> propositions = new HashSet<>();

    private final SMTGeneratingTermVisitor termVisitor;

    public SMTGeneratingFormulaVisitorImpl(SMTGeneratingTermVisitor termVisitor) {
        this.termVisitor = termVisitor;
    }

    @Override
    public String getPredicateDefinitions() {
        StringBuilder sb = new StringBuilder();

        for (Map.Entry<String, Integer> predicate : predicates.entrySet()) {
            String params = StringUtils.repeat(TYPE_NAME, " ", predicate.getValue());
            sb.append(String.format("(declare-fun %s (%s) Bool)\n", predicate.getKey(), params));
        }

        return sb.toString();
    }

    @Override
    public String getTypeDefinition() {
        return predicates.isEmpty() ? "" : "(declare-sort Type)";
    }

    @Override
    public String getPropositionDefinitions() {
        StringBuilder sb = new StringBuilder();

        for (String proposition : propositions) {
            sb.append(String.format("(declare-const %s Bool)", proposition));
        }

        return sb.toString();
    }

    @Override
    public String getConstantDefinitions() {
        StringBuilder sb = new StringBuilder();

        for (String constant : termVisitor.getConstants()) {
            sb.append(String.format("(declare-const %s %s)", constant, TYPE_NAME));
        }

        return sb.toString();
    }

    @Override
    public String getFunctionDefinitions() {
        StringBuilder sb = new StringBuilder();

        for (Map.Entry<String, Integer> function : termVisitor.getFunctions().entrySet()) {
            String name = function.getKey();
            String params = StringUtils.repeat("Type", " ", function.getValue());
            sb.append(String.format("(declare-fun %s (%s) Type)", name, params));
        }

        return sb.toString();
    }

    @Override
    public String visit(Formula formula) {
        return formula.accept(this);
    }

    @Override
    public String visitAndFormula(AndFormula andFormula) {
        Formula left = andFormula.getLeft();
        Formula right = andFormula.getRight();
        return String.format("(and %s %s)", visit(left), visit(right));
    }

    @Override
    public String visitOrFormula(OrFormula orFormula) {
        Formula left = orFormula.getLeft();
        Formula right = orFormula.getRight();
        return String.format("(or %s %s)", visit(left), visit(right));
    }

    @Override
    public String visitForallFormula(ForallFormula forallFormula) {

        StringBuilder sb = new StringBuilder();
        for (Variable variable : forallFormula.getVariables()) {
            sb.append("(").append(variable.getName()).append(" ").append(TYPE_NAME).append(")");
        }
        String vars = sb.toString();

        Formula formula = forallFormula.getFormula();
        return String.format("(forall (%s) %s)", vars, visit(formula));
    }

    @Override
    public String visitExistsFormula(ExistsFormula existsFormula) {
        // Z3 only supports forall. Use equivalence (exists x. foo) === (!(forall x. !foo))
        Map<Type, List<Variable>> variablesByType = existsFormula.getVariablesByType();
        Formula formula = existsFormula.getFormula();
        NotFormula equivalent = new NotFormula(new ForallFormula(variablesByType, new NotFormula(formula)));
        return visit(equivalent);
    }

    @Override
    public String visitTruthFormula(TruthFormula truthFormula) {
        return "true";
    }

    @Override
    public String visitFalsityFormula(FalsityFormula falsityFormula) {
        return "false";
    }

    @Override
    public String visitImpliesFormula(ImpliesFormula impliesFormula) {
        Formula left = impliesFormula.getLeft();
        Formula right = impliesFormula.getRight();
        return String.format("(=> %s %s)", visit(left), visit(right));
    }

    @Override
    public String visitIffFormula(IffFormula iffFormula) {
        Formula left = iffFormula.getLeft();
        Formula right = iffFormula.getRight();
        return String.format("(= %s %s)", visit(left), visit(right));
    }

    @Override
    public String visitNotFormula(NotFormula notFormula) {
        Formula formula = notFormula.getFormula();
        return String.format("(not %s)", visit(formula));
    }

    @Override
    public String visitPropositionFormula(PropositionFormula propositionFormula) {
        String name = propositionFormula.getName();
        propositions.add(name);
        return name;
    }

    @Override
    public String visitPredicateFormula(PredicateFormula predicateFormula) {
        String name = predicateFormula.getName();
        List<Term> params = predicateFormula.getParams();

        predicates.put(name, params.size());

        ArrayList<String> paramStrings = new ArrayList<>();
        for (Term term : params) {
            paramStrings.add(termVisitor.visit(term));
        }

        String paramsString = StringUtils.join(paramStrings, " ");
        return String.format("(%s %s)", name, paramsString);
    }

    @Override
    public String visitEqualToFormula(EqualToFormula equalToFormula) {
        Term left = equalToFormula.getLeft();
        Term right = equalToFormula.getRight();
        return String.format("(= %s %s)", termVisitor.visit(left), termVisitor.visit(right));
    }

    @Override
    public String visitGreaterThanFormula(GreaterThanFormula greaterThanFormula) {
        Term left = greaterThanFormula.getLeft();
        Term right = greaterThanFormula.getRight();
        return String.format("(> %s %s)", termVisitor.visit(left), termVisitor.visit(right));
    }

    @Override
    public String visitLessThanFormula(LessThanFormula lessThanFormula) {
        Term left = lessThanFormula.getLeft();
        Term right = lessThanFormula.getRight();
        return String.format("(< %s %s)", termVisitor.visit(left), termVisitor.visit(right));
    }

    @Override
    public String visitGreaterThanEqualFormula(GreaterThanEqualFormula greaterThanEqualFormula) {
        Term left = greaterThanEqualFormula.getLeft();
        Term right = greaterThanEqualFormula.getRight();
        return String.format("(>= %s %s)", termVisitor.visit(left), termVisitor.visit(right));
    }

    @Override
    public String visitLessThanEqualFormula(LessThanEqualFormula lessThanEqualFormula) {
        Term left = lessThanEqualFormula.getLeft();
        Term right = lessThanEqualFormula.getRight();
        return String.format("(<= %s %s)", termVisitor.visit(left), termVisitor.visit(right));
    }

}

package com.ipandora.core.z3;

import com.ipandora.api.predicate.formula.*;
import com.ipandora.api.predicate.function.FunctionPrototype;
import com.ipandora.api.predicate.term.*;
import com.ipandora.api.predicate.formula.PredicatePrototype;
import com.ipandora.api.predicate.term.Number;
import com.ipandora.core.formula.FormulaConjunctionReducer;
import com.ipandora.core.util.CollectionUtils;
import com.ipandora.core.util.WrappingRuntimeException;
import org.apache.commons.lang3.StringUtils;

import java.util.*;

public class SMTGeneratingFormulaVisitorImpl implements SMTGeneratingFormulaVisitor {

    private final FormulaConjunctionReducer conjunctionReducer;
    private final Map<String, PredicatePrototype> predicatePrototypesByName = new HashMap<>();
    private final Set<String> propositions = new HashSet<>();

    private final SMTGeneratingTermVisitor termVisitor;

    public SMTGeneratingFormulaVisitorImpl(FormulaConjunctionReducer conjunctionReducer,
                                           SMTGeneratingTermVisitor termVisitor) {
        this.conjunctionReducer = conjunctionReducer;
        this.termVisitor = termVisitor;
    }

    @Override
    public List<PredicatePrototype> getPredicatePrototypes() {
        return CollectionUtils.extractMapValues(predicatePrototypesByName);
    }

    @Override
    public Set<String> getPropositionNames() {
        return propositions;
    }

    @Override
    public Map<String, Type> getConstantNamesToTypes() {
        return termVisitor.getConstantNamesToTypes();
    }

    @Override
    public List<FunctionPrototype> getFunctionPrototypes() {
        return termVisitor.getFunctionPrototypes();
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
        List<Variable> natVars = new ArrayList<>();
        for (Variable variable : forallFormula.getVariables()) {
            Type varType = variable.getType();
            if (varType == Type.NAT) {
                natVars.add(variable);
            }
            String type = Z3Sort.forType(varType).getCode();
            sb.append("(").append(variable.getName()).append(" ").append(type).append(")");
        }
        String vars = sb.toString();

        Formula formula = forallFormula.getFormula();

        if (!natVars.isEmpty()) {
            List<Formula> natGuardFormulas = new ArrayList<>();
            for (Variable natVar : natVars) {
                natGuardFormulas.add(new GreaterThanEqualFormula(natVar, new Number(0)));
            }
            Formula natsGuard = conjunctionReducer.reduce(natGuardFormulas);
            formula = new ImpliesFormula(natsGuard, formula);
        }

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
        savePredicate(predicateFormula);

        ArrayList<String> paramStrings = new ArrayList<>();
        for (Term term : predicateFormula.getParams()) {
            paramStrings.add(termVisitor.visit(term));
        }

        String paramsString = StringUtils.join(paramStrings, " ");
        return String.format("(%s %s)", predicateFormula.getName(), paramsString);
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

    private void savePredicate(PredicateFormula predicateFormula) {
        String name = predicateFormula.getName();

        PredicatePrototype newPrototype = PredicatePrototype.fromPredicateFormula(predicateFormula);
        PredicatePrototype existingPrototype = predicatePrototypesByName.get(name);

        if (existingPrototype != null && !existingPrototype.equals(newPrototype)) {

            String errorMsg = String.format("Predicate %s called multiple times with different argument types: " +
                            "One invocation: %s; Another invocation: %s.", name, existingPrototype.getArgTypes(),
                    newPrototype.getArgTypes());
            throw new WrappingRuntimeException(new TypeMismatchException(errorMsg));

        } else if (existingPrototype == null) {
            predicatePrototypesByName.put(name, newPrototype);
        }
    }

}

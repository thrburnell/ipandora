package com.ipandora.core.z3;

import com.ipandora.api.predicate.formula.Formula;
import com.ipandora.core.util.Creator;
import org.apache.commons.lang3.StringUtils;

import java.util.Map;
import java.util.Set;

public class SMTCodeGeneratorImpl implements SMTCodeGenerator {

    private static final String TYPE_NAME = "Type";

    private final Creator<SMTGeneratingFormulaVisitor> visitorCreator;

    public SMTCodeGeneratorImpl(Creator<SMTGeneratingFormulaVisitor> visitorCreator) {
        this.visitorCreator = visitorCreator;
    }

    @Override
    public String generateCheckSatCode(Formula formula) {

        StringBuilder sb = new StringBuilder();

        SMTGeneratingFormulaVisitor visitor = visitorCreator.create();
        String formulaCode = visitor.visit(formula);

        appendTypeDefinition(sb);
        appendPredicateDefinitions(visitor.getPredicateNamesToArgCount(), sb);
        appendPropositionDefinitions(visitor.getPropositionNames(), sb);
        appendConstantDefinitions(visitor.getConstantNames(), sb);
        appendFunctionDefinitions(visitor.getFunctionNamesToArgCount(), sb);

        sb.append("(assert ").append(formulaCode).append(") (check-sat)");

        return sb.toString();
    }

    private StringBuilder appendTypeDefinition(StringBuilder sb) {
        return sb.append("(declare-sort ").append(TYPE_NAME).append(")");
    }

    private StringBuilder appendPredicateDefinitions(Map<String, Integer> predicateNamesToArgCount, StringBuilder sb) {

        for (Map.Entry<String, Integer> predicate : predicateNamesToArgCount.entrySet()) {
            String params = StringUtils.repeat(TYPE_NAME, " ", predicate.getValue());
            sb.append(String.format("(declare-fun %s (%s) Bool)\n", predicate.getKey(), params));
        }

        return sb;
    }

    private StringBuilder appendPropositionDefinitions(Set<String> propositionNames, StringBuilder sb) {

        for (String proposition : propositionNames) {
            sb.append(String.format("(declare-const %s Bool)", proposition));
        }

        return sb;
    }

    private StringBuilder appendConstantDefinitions(Set<String> constantNames, StringBuilder sb) {

        for (String constant : constantNames) {
            sb.append(String.format("(declare-const %s %s)", constant, TYPE_NAME));
        }

        return sb;
    }

    private StringBuilder appendFunctionDefinitions(Map<String, Integer> functionNamesToArgCount, StringBuilder sb) {

        for (Map.Entry<String, Integer> function : functionNamesToArgCount.entrySet()) {
            String name = function.getKey();
            String params = StringUtils.repeat("Type", " ", function.getValue());
            sb.append(String.format("(declare-fun %s (%s) Type)", name, params));
        }

        return sb;
    }

}

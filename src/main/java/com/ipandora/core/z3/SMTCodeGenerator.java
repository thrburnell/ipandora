package com.ipandora.core.z3;

import com.ipandora.api.predicate.formula.Formula;

public class SMTCodeGenerator {

    private final SMTGeneratingFormulaVisitor visitor;

    public SMTCodeGenerator(SMTGeneratingFormulaVisitor visitor) {
        this.visitor = visitor;
    }

    public String checkSat(Formula formula) {
        String formulaCode = visitor.visit(formula);
        String typeDefinition = visitor.getTypeDefinition();
        String predicateDefinitions = visitor.getPredicateDefinitions();
        return typeDefinition + predicateDefinitions + "(assert " + formulaCode + ")" + "(check-sat)";
    }

}

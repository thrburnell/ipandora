package com.ipandora.core.z3;

import com.ipandora.api.predicate.formula.Formula;

public class SMTCodeGeneratorImpl implements SMTCodeGenerator {

    private final SMTGeneratingFormulaVisitor visitor;

    public SMTCodeGeneratorImpl(SMTGeneratingFormulaVisitor visitor) {
        this.visitor = visitor;
    }

    @Override
    public String generateCheckSatCode(Formula formula) {
        String formulaCode = visitor.visit(formula);
        String typeDefinition = visitor.getTypeDefinition();
        String predicateDefinitions = visitor.getPredicateDefinitions();
        return typeDefinition + predicateDefinitions + "(assert " + formulaCode + ")" + "(check-sat)";
    }

}

package com.ipandora.core.z3;

import com.ipandora.api.predicate.formula.Formula;
import com.ipandora.core.util.Creator;

public class SMTCodeGeneratorImpl implements SMTCodeGenerator {

    private final Creator<SMTGeneratingFormulaVisitor> visitorCreator;

    public SMTCodeGeneratorImpl(Creator<SMTGeneratingFormulaVisitor> visitorCreator) {
        this.visitorCreator = visitorCreator;
    }

    @Override
    public String generateCheckSatCode(Formula formula) {
        SMTGeneratingFormulaVisitor visitor = visitorCreator.create();
        String formulaCode = visitor.visit(formula);
        String typeDefinition = visitor.getTypeDefinition();
        String predicateDefinitions = visitor.getPredicateDefinitions();
        String propositionDefinitions = visitor.getPropositionDefinitions();
        String constantDefinitions = visitor.getConstantDefinitions();
        return typeDefinition + predicateDefinitions + propositionDefinitions + constantDefinitions +
                "(assert " + formulaCode + ")" + "(check-sat)";
    }

}

package com.ipandora.core.z3;

import com.ipandora.core.formula.FormulaConjunctionReducer;
import com.ipandora.core.util.Creator;

public class SMTGeneratingFormulaVisitorCreator implements Creator<SMTGeneratingFormulaVisitor> {

    @Override
    public SMTGeneratingFormulaVisitor create() {
        return new SMTGeneratingFormulaVisitorImpl(new FormulaConjunctionReducer(), new SMTGeneratingTermVisitor());
    }

}

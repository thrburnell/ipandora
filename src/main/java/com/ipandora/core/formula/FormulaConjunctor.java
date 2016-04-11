package com.ipandora.core.formula;

import com.ipandora.api.predicate.formula.AndFormula;
import com.ipandora.api.predicate.formula.Formula;

import java.util.List;

public class FormulaConjunctor {

    public Formula join(List<Formula> formulas) {

        if (formulas.isEmpty()) {
            return null;
        }

        Formula formula = formulas.get(0);
        for (int i = 1; i < formulas.size(); i++) {
            formula = new AndFormula(formula, formulas.get(i));
        }

        return formula;
    }

}

package com.ipandora.core.formula;

import com.ipandora.api.predicate.formula.AndFormula;
import com.ipandora.api.predicate.formula.Formula;

import java.util.ArrayList;
import java.util.List;

public class ConjunctionFormulaSplitter implements FormulaSplitter<AndFormula> {

    @Override
    public List<Formula> split(AndFormula formula) {

        List<Formula> formulas = new ArrayList<>();

        if (formula != null) {

            Formula left = formula.getLeft();
            if (left instanceof AndFormula) {
                formulas.addAll(split((AndFormula) left));
            } else {
                formulas.add(left);
            }

            Formula right = formula.getRight();
            if (right instanceof AndFormula) {
                formulas.addAll(split((AndFormula) right));
            } else {
                formulas.add(right);
            }
        }

        return formulas;
    }

}

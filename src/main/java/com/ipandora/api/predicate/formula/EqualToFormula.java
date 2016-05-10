package com.ipandora.api.predicate.formula;

import com.ipandora.api.predicate.term.Term;
import com.ipandora.core.formula.FormulaVisitor;

public class EqualToFormula extends MathematicalComparisonFormula {

    public EqualToFormula(Term left, Term right) {
        super(left, right);
    }

    @Override
    public <T> T accept(FormulaVisitor<T> visitor) {
        return visitor.visitEqualToFormula(this);
    }

    @Override
    public String toString() {
        return String.format("%s = %s", left, right);
    }

}

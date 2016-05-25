package com.ipandora.api.predicate.function;

import com.ipandora.api.predicate.formula.Formula;
import com.ipandora.api.predicate.term.Term;

public class FunctionCase {

    private final Term expression;
    private final Formula condition;

    public FunctionCase(Term expression, Formula condition) {
        this.expression = expression;
        this.condition = condition;
    }

    public Term getExpression() {
        return expression;
    }

    public Formula getCondition() {
        return condition;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        FunctionCase that = (FunctionCase) o;

        if (!expression.equals(that.expression)) return false;
        return condition.equals(that.condition);
    }

    @Override
    public int hashCode() {
        int result = expression.hashCode();
        result = 31 * result + condition.hashCode();
        return result;
    }

}

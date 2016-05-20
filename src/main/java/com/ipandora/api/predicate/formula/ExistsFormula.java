package com.ipandora.api.predicate.formula;

import com.ipandora.api.predicate.term.Type;
import com.ipandora.api.predicate.term.Variable;
import com.ipandora.core.formula.FormulaVisitor;
import org.apache.commons.lang3.StringUtils;

import java.util.List;
import java.util.Map;

public class ExistsFormula extends QuantifiedFormula {

    public ExistsFormula(Map<Type, List<Variable>> variablesByType, Formula formula) {
        super(variablesByType, formula);
    }

    public ExistsFormula(Variable variable, Formula formula) {
        super(variable, formula);
    }

    public ExistsFormula(Formula formula, Variable... variables) {
        super(formula, variables);
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("\u2203");
        for (Map.Entry<Type, List<Variable>> entry : variablesByType.entrySet()) {
            Type type = entry.getKey();
            String varNames = StringUtils.join(entry.getValue(), ",");
            String typeString = type == null ? "" : String.format("\u2208%s", type);
            sb.append(varNames).append(typeString);
        }
        sb.append(" ").append(formula);

        return sb.toString();
    }

    @Override
    public <T> T accept(FormulaVisitor<T> visitor) {
        return visitor.visitExistsFormula(this);
    }

}

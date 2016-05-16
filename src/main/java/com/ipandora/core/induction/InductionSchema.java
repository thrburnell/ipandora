package com.ipandora.core.induction;

import com.ipandora.api.predicate.formula.Formula;
import com.ipandora.api.predicate.term.Constant;

import java.util.List;

public class InductionSchema {

    private final List<Formula> baseCaseToShow;
    private final Constant inductiveTerm;
    private final Formula inductiveHypothesis;
    private final List<Formula> inductiveCaseToShow;

    public InductionSchema(List<Formula> baseCaseToShow, Constant inductiveTerm, Formula inductiveHypothesis,
                           List<Formula> inductiveCaseToShow) {
        this.baseCaseToShow = baseCaseToShow;
        this.inductiveTerm = inductiveTerm;
        this.inductiveHypothesis = inductiveHypothesis;
        this.inductiveCaseToShow = inductiveCaseToShow;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("Base Case\n");
        sb.append("To Show:\n");
        for (int i = 0; i < baseCaseToShow.size(); i++) {
            sb.append("(").append(i).append(") ");
            sb.append(baseCaseToShow.get(i)).append("\n");
        }

        sb.append("\n").append("Inductive Step:\n");
        sb.append("Take ").append(inductiveTerm).append(" arbitrary.\n\n");
        sb.append("Inductive Hypothesis: ").append(inductiveHypothesis).append("\n");
        sb.append("To Show:\n");
        for (int i = 0; i < inductiveCaseToShow.size(); i++) {
            sb.append("(").append(i).append(") ");
            sb.append(inductiveCaseToShow.get(i)).append("\n");
        }

        return sb.toString();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        InductionSchema that = (InductionSchema) o;

        if (!baseCaseToShow.equals(that.baseCaseToShow)) return false;
        if (!inductiveTerm.equals(that.inductiveTerm)) return false;
        if (!inductiveHypothesis.equals(that.inductiveHypothesis)) return false;
        return inductiveCaseToShow.equals(that.inductiveCaseToShow);
    }

    @Override
    public int hashCode() {
        int result = baseCaseToShow.hashCode();
        result = 31 * result + inductiveTerm.hashCode();
        result = 31 * result + inductiveHypothesis.hashCode();
        result = 31 * result + inductiveCaseToShow.hashCode();
        return result;
    }

}

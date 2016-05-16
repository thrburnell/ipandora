package com.ipandora.core.formula;

import com.ipandora.api.predicate.formula.EqualToFormula;
import com.ipandora.api.predicate.formula.ForallFormula;
import com.ipandora.api.predicate.formula.Formula;
import com.ipandora.api.predicate.formula.GreaterThanFormula;
import com.ipandora.api.predicate.term.*;
import com.ipandora.api.predicate.term.Number;
import org.junit.Test;

import static org.assertj.core.api.Assertions.assertThat;

public class TermSubstitutorTest {

    private static final Variable N_NAT = Variable.withTypeNat("?n");
    private static final Variable M_NAT = Variable.withTypeNat("?m");
    private static final Variable P_NAT = Variable.withTypeNat("?p");
    private static final Variable Q_NAT = Variable.withTypeNat("?q");
    private static final Variable X_NAT = Variable.withTypeNat("?x");

    private static final Number NUM_2 = new Number(2);
    private static final Number NUM_3 = new Number(3);

    @Test
    public void cloneAndSubstituteInScopeSimpleEquality() {
        // n = 2
        TermSubstitutor substitutor = new TermSubstitutor();

        EqualToFormula equalToFormula = new EqualToFormula(N_NAT, NUM_2);
        Formula substituted = substitutor.cloneAndSubstituteInScope(equalToFormula, N_NAT, M_NAT);
        EqualToFormula expected = new EqualToFormula(M_NAT, NUM_2);

        assertThat(substituted).isEqualTo(expected);
    }

    @Test
    public void cloneAndSubstituteInScopeNestedArithmetic() {
        // ?n + ?m + 3 > 3 * (?n + ?p) / ?q + ?n
        TermSubstitutor substitutor = new TermSubstitutor();

        Addition addition = new Addition(new Addition(N_NAT, M_NAT), NUM_3);
        Division division = new Division(new Multiplication(NUM_3, new Addition(N_NAT, P_NAT)), new Addition(Q_NAT, N_NAT));

        Addition subAddition = new Addition(new Addition(X_NAT, M_NAT), NUM_3);
        Division subDivision = new Division(new Multiplication(NUM_3, new Addition(X_NAT, P_NAT)), new Addition(Q_NAT, X_NAT));

        GreaterThanFormula greaterThanFormula = new GreaterThanFormula(addition, division);
        Formula substituted = substitutor.cloneAndSubstituteInScope(greaterThanFormula, N_NAT, X_NAT);
        GreaterThanFormula expected = new GreaterThanFormula(subAddition, subDivision);

        assertThat(substituted).isEqualTo(expected);
    }

    @Test
    public void cloneAndSubstituteInScopeShouldntSubstituteNewlyScopedVariables() {
        // \FORALL ?n ?n = 2
        TermSubstitutor substitutor = new TermSubstitutor();

        ForallFormula original = new ForallFormula(N_NAT, new EqualToFormula(N_NAT, NUM_2));
        Formula substituted = substitutor.cloneAndSubstituteInScope(original, N_NAT, M_NAT);

        assertThat(substituted).isEqualTo(original);
    }

    @Test
    public void cloneAndSubstituteInScopeShouldSubstituteVariablesInNewScopeNotQuantifiedByNewScope() {
        // \FORALL ?n ?n > ?m

        TermSubstitutor substitutor = new TermSubstitutor();

        ForallFormula forallFormula = new ForallFormula(N_NAT, new GreaterThanFormula(N_NAT, M_NAT));
        Formula substituted = substitutor.cloneAndSubstituteInScope(forallFormula, M_NAT, X_NAT);
        ForallFormula expected = new ForallFormula(N_NAT, new GreaterThanFormula(N_NAT, X_NAT));

        assertThat(substituted).isEqualTo(expected);
    }

    @Test
    public void cloneAndSubstituteInScopeShouldntSubstituteNewlyScopedVariablesNested() {
        // \FORALL ?n \FORALL ?m ?n = ?m

        TermSubstitutor substitutor = new TermSubstitutor();

        ForallFormula original = new ForallFormula(N_NAT,
                new ForallFormula(M_NAT, new EqualToFormula(N_NAT, M_NAT)));

        Formula substituted = substitutor.cloneAndSubstituteInScope(original, M_NAT, X_NAT);

        assertThat(substituted).isEqualTo(original);
    }

    @Test
    public void cloneAndSubstituteInScopeShouldntSubstituteNewlyScopedVariableNested() {
        // \FORALL ?n \FORALL ?n \FORALL ?n ?n = 2

        TermSubstitutor substitutor = new TermSubstitutor();

        ForallFormula original = new ForallFormula(N_NAT,
                new ForallFormula(N_NAT, new ForallFormula(N_NAT, new EqualToFormula(N_NAT, NUM_2))));

        Formula substituted = substitutor.cloneAndSubstituteInScope(original, N_NAT, X_NAT);

        assertThat(substituted).isEqualTo(original);
    }

}

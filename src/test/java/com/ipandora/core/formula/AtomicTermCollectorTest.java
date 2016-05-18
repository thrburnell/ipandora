package com.ipandora.core.formula;

import com.ipandora.api.predicate.formula.AndFormula;
import com.ipandora.api.predicate.formula.EqualToFormula;
import com.ipandora.api.predicate.formula.PredicateFormula;
import com.ipandora.api.predicate.term.*;
import com.ipandora.api.predicate.term.Number;
import org.junit.Test;

import java.util.Arrays;
import java.util.Set;

import static org.assertj.core.api.Assertions.assertThat;

public class AtomicTermCollectorTest {

    public static final Variable X = new Variable("x");
    public static final Constant Y = new Constant("y");
    public static final Variable Z = new Variable("z");
    public static final Number N_1 = new Number(1);
    public static final Number N_14 = new Number(14);

    @Test
    public void collectAtomsAndFormula() {
        AtomicTermCollector collector = new AtomicTermCollector();
        Set<Atom> atoms = collector.collectAtoms(new AndFormula(
                new EqualToFormula(X, Y),
                new PredicateFormula("Foo", Arrays.<Term>asList(N_1, N_14, Z))));

        assertThat(atoms).hasSize(5);
        assertThat(atoms).contains(X);
        assertThat(atoms).contains(Y);
        assertThat(atoms).contains(Z);

        assertThat(atoms).contains(N_1);
        assertThat(atoms).contains(N_14);
    }

}

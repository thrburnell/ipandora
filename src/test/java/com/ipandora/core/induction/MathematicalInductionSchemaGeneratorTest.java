package com.ipandora.core.induction;

import com.ipandora.api.predicate.formula.*;
import com.ipandora.api.predicate.term.*;
import com.ipandora.api.predicate.term.Number;
import com.ipandora.core.formula.TermSubstitutor;
import com.ipandora.core.term.TermStringBuilder;
import org.junit.Before;
import org.junit.Test;

import java.util.Collections;

import static org.assertj.core.api.Assertions.assertThat;

public class MathematicalInductionSchemaGeneratorTest {

    private static final Variable K_NAT = Variable.withTypeNat("k");
    private static final Variable K1_NAT = Variable.withTypeNat("k1");
    private static final Variable K2_NAT = Variable.withTypeNat("k2");
    private static final Variable N_NAT = Variable.withTypeNat("n");
    private static final Variable M_NAT = Variable.withTypeNat("m");
    private static final Number ZERO = new Number(0);
    private static final Number ONE = new Number(1);
    private static final Number TWO = new Number(2);
    private static final Variable X_UNKNOWN = new Variable("x");

    private TermStringBuilder termStringBuilder;
    private TermSubstitutor termSubstitutor;

    @Before
    public void before() {
        termStringBuilder = new TermStringBuilder();
        termSubstitutor = new TermSubstitutor();
    }

    @Test
    public void generateSchemaSimpleEquality() throws SchemaGeneratorException {
        // \FORALL n in Nat. n = n

        EqualToFormula baseCase = new EqualToFormula(ZERO, ZERO);
        EqualToFormula indHyp = new EqualToFormula(K_NAT, K_NAT);
        EqualToFormula inductiveCase = new EqualToFormula(new Addition(K_NAT, ONE), new Addition(K_NAT, ONE));

        InductionSchema expected = new InductionSchema(
                Collections.<Formula>singletonList(baseCase), K_NAT, indHyp,
                Collections.<Formula>singletonList(inductiveCase));

        ForallFormula forallFormula = new ForallFormula(N_NAT, new EqualToFormula(N_NAT, N_NAT));

        MathematicalInductionSchemaGenerator generator =
                new MathematicalInductionSchemaGenerator(termStringBuilder, termSubstitutor);
        InductionSchema inductionSchema = generator.generateSchema(forallFormula, N_NAT);

        assertThat(inductionSchema).isEqualTo(expected);
    }

    @Test
    public void generateSchemaInequalityWithAddition() throws SchemaGeneratorException {
        // \FORALL n in Nat. (?n + 2 > ?n + 1)
        GreaterThanFormula baseCase = new GreaterThanFormula(new Addition(ZERO, TWO), new Addition(ZERO, ONE));
        GreaterThanFormula indHyp = new GreaterThanFormula(new Addition(K_NAT, TWO), new Addition(K_NAT, ONE));

        GreaterThanFormula inductiveCase = new GreaterThanFormula(
                new Addition(new Addition(K_NAT, ONE), TWO), new Addition(new Addition(K_NAT, ONE), ONE));

        InductionSchema expected = new InductionSchema(Collections.<Formula>singletonList(baseCase), K_NAT,
                indHyp, Collections.<Formula>singletonList(inductiveCase));

        ForallFormula forallFormula = new ForallFormula(N_NAT,
                new GreaterThanFormula(new Addition(N_NAT, TWO), new Addition(N_NAT, ONE)));

        MathematicalInductionSchemaGenerator generator =
                new MathematicalInductionSchemaGenerator(termStringBuilder, termSubstitutor);
        InductionSchema inductionSchema = generator.generateSchema(forallFormula, N_NAT);

        assertThat(inductionSchema).isEqualTo(expected);
    }

    @Test
    public void generateSchemaNestedForallWithDifferentVariable() throws SchemaGeneratorException {
        // \FORALL n in Nat. \FORALL m in Nat. (n > m -> n + 1 > m + 1)

        ForallFormula baseCase = new ForallFormula(M_NAT, new ImpliesFormula(
                new GreaterThanFormula(ZERO, M_NAT),
                new GreaterThanFormula(new Addition(ZERO, ONE), new Addition(M_NAT, ONE))));

        ForallFormula indHyp = new ForallFormula(M_NAT, new ImpliesFormula(
                new GreaterThanFormula(K_NAT, M_NAT),
                new GreaterThanFormula(new Addition(K_NAT, ONE), new Addition(M_NAT, ONE))));

        ForallFormula inductiveCase = new ForallFormula(M_NAT, new ImpliesFormula(
                new GreaterThanFormula(new Addition(K_NAT, ONE), M_NAT),
                new GreaterThanFormula(new Addition(new Addition(K_NAT, ONE), ONE), new Addition(M_NAT, ONE))));

        InductionSchema expected = new InductionSchema(Collections.<Formula>singletonList(baseCase), K_NAT,
                indHyp, Collections.<Formula>singletonList(inductiveCase));

        // Create the forall formula

        ForallFormula inner = new ForallFormula(M_NAT, new ImpliesFormula(
                new GreaterThanFormula(N_NAT, M_NAT),
                new GreaterThanFormula(new Addition(N_NAT, ONE), new Addition(M_NAT, ONE))));

        ForallFormula forallFormula = new ForallFormula(N_NAT, inner);

        MathematicalInductionSchemaGenerator generator =
                new MathematicalInductionSchemaGenerator(termStringBuilder, termSubstitutor);
        InductionSchema inductionSchema = generator.generateSchema(forallFormula, N_NAT);

        assertThat(inductionSchema).isEqualTo(expected);
    }

    @Test
    public void generateSchemaNestedForallWithSameVariable() throws SchemaGeneratorException {
        // \FORALL n in Nat. \FORALL n in Nat (2 * n = n + n)

        ForallFormula inner = new ForallFormula(N_NAT,
                new EqualToFormula(new Multiplication(TWO, N_NAT), new Addition(N_NAT, N_NAT)));

        InductionSchema expected = new InductionSchema(Collections.<Formula>singletonList(inner), K_NAT,
                inner, Collections.<Formula>singletonList(inner));

        ForallFormula forallFormula = new ForallFormula(N_NAT, inner);

        MathematicalInductionSchemaGenerator generator =
                new MathematicalInductionSchemaGenerator(termStringBuilder, termSubstitutor);
        InductionSchema inductionSchema = generator.generateSchema(forallFormula, N_NAT);

        assertThat(inductionSchema).isEqualTo(expected);
    }

    @Test(expected = SchemaGeneratorException.class)
    public void generateSchemaShouldThrowIfVariableNotOfTypeNat() throws SchemaGeneratorException {
        // \FORALL n. n = n

        Variable untypedVar = new Variable("n");
        ForallFormula forallFormula = new ForallFormula(untypedVar, new EqualToFormula(untypedVar, untypedVar));

        MathematicalInductionSchemaGenerator generator =
                new MathematicalInductionSchemaGenerator(termStringBuilder, termSubstitutor);
        generator.generateSchema(forallFormula, N_NAT);
    }

    @Test
    public void generateSchemaShouldUseK2IfKAndK1NamesAlreadyUsed() throws SchemaGeneratorException {
        // \FORALL k in Nat. \FORALL k1 in Nat. (k + k1 = 2)
        ForallFormula inner = new ForallFormula(K1_NAT, new EqualToFormula(new Addition(K_NAT, K1_NAT), new Number(2)));
        ForallFormula forallFormula = new ForallFormula(K_NAT, inner);

        MathematicalInductionSchemaGenerator generator =
                new MathematicalInductionSchemaGenerator(termStringBuilder, termSubstitutor);

        InductionSchema inductionSchema = generator.generateSchema(forallFormula, K_NAT);
        Variable inductiveTerm = inductionSchema.getInductiveTerm();

        assertThat(inductiveTerm).isEqualTo(K2_NAT);
    }

    @Test
    public void generateSchemaShouldUseK1IfKAlreadyUsedAsQuantifiedVariable() throws SchemaGeneratorException {
        // \FORALL m, k in Nat. m + k = 0

        ForallFormula baseCase = new ForallFormula(new EqualToFormula(new Addition(ZERO, K_NAT), ZERO), K_NAT);
        ForallFormula indHyp = new ForallFormula(new EqualToFormula(new Addition(K1_NAT, K_NAT), ZERO), K_NAT);
        ForallFormula indCase = new ForallFormula(new EqualToFormula(
                new Addition(new Addition(K1_NAT, ONE), K_NAT), ZERO), K_NAT);

        InductionSchema expected = new InductionSchema(Collections.<Formula>singletonList(baseCase), K1_NAT,
                indHyp, Collections.<Formula>singletonList(indCase));

        ForallFormula forallFormula = new ForallFormula(
                new EqualToFormula(new Addition(M_NAT, K_NAT), ZERO), M_NAT, K_NAT);

        MathematicalInductionSchemaGenerator generator =
                new MathematicalInductionSchemaGenerator(termStringBuilder, termSubstitutor);

        InductionSchema inductionSchema = generator.generateSchema(forallFormula, M_NAT);

        assertThat(inductionSchema).isEqualTo(expected);
    }

    @Test
    public void generateSchemaShouldLeaveQuantifiedVariablesIntactIfMultipleQuantVars() throws SchemaGeneratorException {
        // \FORALL m, n in Nat, x. m > n

        ForallFormula baseCase = new ForallFormula(new GreaterThanFormula(M_NAT, ZERO), M_NAT, X_UNKNOWN);
        ForallFormula indHyp = new ForallFormula(new GreaterThanFormula(M_NAT, K_NAT), M_NAT, X_UNKNOWN);
        ForallFormula indCase = new ForallFormula(new GreaterThanFormula(M_NAT, new Addition(K_NAT, ONE)),
                M_NAT, X_UNKNOWN);

        InductionSchema expected = new InductionSchema(Collections.<Formula>singletonList(baseCase), K_NAT, indHyp,
                Collections.<Formula>singletonList(indCase));

        ForallFormula forallFormula = new ForallFormula(new GreaterThanFormula(M_NAT, N_NAT), M_NAT, N_NAT, X_UNKNOWN);

        MathematicalInductionSchemaGenerator generator =
                new MathematicalInductionSchemaGenerator(termStringBuilder, termSubstitutor);

        InductionSchema inductionSchema = generator.generateSchema(forallFormula, N_NAT);

        assertThat(inductionSchema).isEqualTo(expected);
    }

}

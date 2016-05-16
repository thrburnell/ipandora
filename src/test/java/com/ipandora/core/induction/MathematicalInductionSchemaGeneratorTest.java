package com.ipandora.core.induction;

import com.ipandora.api.predicate.formula.*;
import com.ipandora.api.predicate.term.*;
import com.ipandora.api.predicate.term.Number;
import com.ipandora.core.formula.TermSubstitutor;
import org.junit.Test;

import java.util.Collections;

import static org.assertj.core.api.Assertions.assertThat;

public class MathematicalInductionSchemaGeneratorTest {

    private static final Constant K = new Constant("k");
    private static final Number ZERO = new Number(0);
    private static final Number ONE = new Number(1);
    private static final Number TWO = new Number(2);
    private static final Variable N_NAT = Variable.withTypeNat("?n");
    private static final Variable M_NAT = Variable.withTypeNat("?m");
    private static final Variable I_NAT = Variable.withTypeNat("?i");

    @Test
    public void generateSchemaSimpleEquality() throws SchemaGeneratorException {
        // \FORALL ?n in Nat ?n = ?n

        EqualToFormula baseCase = new EqualToFormula(ZERO, ZERO);
        EqualToFormula indHyp = new EqualToFormula(K, K);
        EqualToFormula inductiveCase = new EqualToFormula(new Addition(K, ONE), new Addition(K, ONE));

        InductionSchema expected = new InductionSchema(
                Collections.<Formula>singletonList(baseCase), K, indHyp,
                Collections.<Formula>singletonList(inductiveCase));

        ForallFormula forallFormula = new ForallFormula(N_NAT, new EqualToFormula(N_NAT, N_NAT));

        TermSubstitutor termSubstitutor = new TermSubstitutor();
        MathematicalInductionSchemaGenerator generator = new MathematicalInductionSchemaGenerator(termSubstitutor);
        InductionSchema inductionSchema = generator.generateSchema(forallFormula);

        assertThat(inductionSchema).isEqualTo(expected);
    }

    @Test
    public void generateSchemaInequalityWithAddition() throws SchemaGeneratorException {
        // \FORALL ?n in Nat (?n + 2 > ?n + 1)
        GreaterThanFormula baseCase = new GreaterThanFormula(new Addition(ZERO, TWO), new Addition(ZERO, ONE));
        GreaterThanFormula indHyp = new GreaterThanFormula(new Addition(K, TWO), new Addition(K, ONE));

        GreaterThanFormula inductiveCase = new GreaterThanFormula(
                new Addition(new Addition(K, ONE), TWO), new Addition(new Addition(K, ONE), ONE));

        InductionSchema expected = new InductionSchema(Collections.<Formula>singletonList(baseCase), K,
                indHyp, Collections.<Formula>singletonList(inductiveCase));

        ForallFormula forallFormula = new ForallFormula(N_NAT,
                new GreaterThanFormula(new Addition(N_NAT, TWO), new Addition(N_NAT, ONE)));

        TermSubstitutor termSubstitutor = new TermSubstitutor();
        MathematicalInductionSchemaGenerator generator = new MathematicalInductionSchemaGenerator(termSubstitutor);
        InductionSchema inductionSchema = generator.generateSchema(forallFormula);

        assertThat(inductionSchema).isEqualTo(expected);
    }

    @Test
    public void generateSchemaEqualityWithSummation() throws SchemaGeneratorException {
        // \FORALL ?n in Nat (\SUM ?i 0 ?n ?i^2 = ?n * (?n + 1) * (2 * ?n + 1)

        Summation baseSum = new Summation(I_NAT, ZERO, ZERO, new Power(I_NAT, 2));

        Multiplication baseMult = new Multiplication(
                new Multiplication(ZERO, new Addition(ZERO, ONE)), new Addition(new Multiplication(TWO, ZERO), ONE));

        EqualToFormula baseCase = new EqualToFormula(baseSum, baseMult);

        Summation indHypSum = new Summation(I_NAT, ZERO, K, new Power(I_NAT, 2));

        Multiplication indHypMult = new Multiplication(
                new Multiplication(K, new Addition(K, ONE)), new Addition(new Multiplication(TWO, K), ONE));

        EqualToFormula indHyp = new EqualToFormula(indHypSum, indHypMult);

        Summation indCaseSum = new Summation(I_NAT, ZERO, new Addition(K, ONE), new Power(I_NAT, 2));

        Multiplication indCaseMult = new Multiplication(
                new Multiplication(new Addition(K, ONE), new Addition(new Addition(K, ONE), ONE)),
                new Addition(new Multiplication(TWO, new Addition(K, ONE)), ONE));

        EqualToFormula inductiveCase = new EqualToFormula(indCaseSum, indCaseMult);

        InductionSchema expected = new InductionSchema(Collections.<Formula>singletonList(baseCase), K,
                indHyp, Collections.<Formula>singletonList(inductiveCase));

        // Create the forall formula

        Multiplication multiplication = new Multiplication(
                new Multiplication(N_NAT, new Addition(N_NAT, ONE)),
                new Addition(new Multiplication(TWO, N_NAT), ONE));

        Summation summation = new Summation(I_NAT, ZERO, N_NAT, new Power(I_NAT, 2));

        ForallFormula forallFormula = new ForallFormula(N_NAT, new EqualToFormula(summation, multiplication));

        TermSubstitutor termSubstitutor = new TermSubstitutor();
        MathematicalInductionSchemaGenerator generator = new MathematicalInductionSchemaGenerator(termSubstitutor);
        InductionSchema inductionSchema = generator.generateSchema(forallFormula);

        assertThat(inductionSchema).isEqualTo(expected);
    }

    @Test
    public void generateSchemaNestedForallWithDifferentVariable() throws SchemaGeneratorException {
        // \FORALL ?n in Nat \FORALL ?m in Nat (?n > ?m -> ?n + 1 > ?m + 1)

        ForallFormula baseCase = new ForallFormula(M_NAT, new ImpliesFormula(
                new GreaterThanFormula(ZERO, M_NAT),
                new GreaterThanFormula(new Addition(ZERO, ONE), new Addition(M_NAT, ONE))));

        ForallFormula indHyp = new ForallFormula(M_NAT, new ImpliesFormula(
                new GreaterThanFormula(K, M_NAT),
                new GreaterThanFormula(new Addition(K, ONE), new Addition(M_NAT, ONE))));

        ForallFormula inductiveCase = new ForallFormula(M_NAT, new ImpliesFormula(
                new GreaterThanFormula(new Addition(K, ONE), M_NAT),
                new GreaterThanFormula(new Addition(new Addition(K, ONE), ONE), new Addition(M_NAT, ONE))));

        InductionSchema expected = new InductionSchema(Collections.<Formula>singletonList(baseCase), K,
                indHyp, Collections.<Formula>singletonList(inductiveCase));

        // Create the forall formula

        ForallFormula inner = new ForallFormula(M_NAT, new ImpliesFormula(
                new GreaterThanFormula(N_NAT, M_NAT),
                new GreaterThanFormula(new Addition(N_NAT, ONE), new Addition(M_NAT, ONE))));

        ForallFormula forallFormula = new ForallFormula(N_NAT, inner);

        TermSubstitutor termSubstitutor = new TermSubstitutor();
        MathematicalInductionSchemaGenerator generator = new MathematicalInductionSchemaGenerator(termSubstitutor);
        InductionSchema inductionSchema = generator.generateSchema(forallFormula);

        assertThat(inductionSchema).isEqualTo(expected);
    }

    @Test
    public void generateSchemaNestedForallWithSameVariable() throws SchemaGeneratorException {
        // \FORALL ?n in Nat \FORALL ?n in Nat (2 * ?n = ?n + ?n)

        ForallFormula inner = new ForallFormula(N_NAT,
                new EqualToFormula(new Multiplication(TWO, N_NAT), new Addition(N_NAT, N_NAT)));

        InductionSchema expected = new InductionSchema(Collections.<Formula>singletonList(inner), K,
                inner, Collections.<Formula>singletonList(inner));

        ForallFormula forallFormula = new ForallFormula(N_NAT, inner);

        TermSubstitutor termSubstitutor = new TermSubstitutor();
        MathematicalInductionSchemaGenerator generator = new MathematicalInductionSchemaGenerator(termSubstitutor);
        InductionSchema inductionSchema = generator.generateSchema(forallFormula);

        assertThat(inductionSchema).isEqualTo(expected);
    }

    @Test(expected = SchemaGeneratorException.class)
    public void generateSchemaShouldThrowIfVariableNotOfTypeNat() throws SchemaGeneratorException {
        // \FORALL ?n ?n = ?n

        Variable untypedVar = new Variable("?n");
        ForallFormula forallFormula = new ForallFormula(untypedVar, new EqualToFormula(untypedVar, untypedVar));

        TermSubstitutor termSubstitutor = new TermSubstitutor();
        MathematicalInductionSchemaGenerator generator = new MathematicalInductionSchemaGenerator(termSubstitutor);
        generator.generateSchema(forallFormula);
    }

}

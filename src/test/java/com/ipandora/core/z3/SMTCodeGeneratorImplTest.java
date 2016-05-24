package com.ipandora.core.z3;

import com.ipandora.api.predicate.formula.Formula;
import com.ipandora.api.predicate.formula.TruthFormula;
import com.ipandora.api.predicate.function.FunctionPrototype;
import com.ipandora.api.predicate.formula.PredicatePrototype;
import com.ipandora.api.predicate.term.Type;
import com.ipandora.api.predicate.term.TypeMismatchException;
import com.ipandora.core.util.WrappingRuntimeException;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.mockito.Mock;
import org.mockito.runners.MockitoJUnitRunner;

import java.util.*;

import static org.assertj.core.api.Assertions.assertThat;
import static org.mockito.Matchers.any;
import static org.mockito.Mockito.when;

@RunWith(MockitoJUnitRunner.class)
public class SMTCodeGeneratorImplTest {

    @Mock
    private SMTGeneratingFormulaVisitor mockSmtGeneratingFormulaVisitor;

    @Mock
    private SMTGeneratingFormulaVisitorCreator mockSmtGeneratingFormulaVisitorCreator;

    @Before
    public void before() {
        when(mockSmtGeneratingFormulaVisitorCreator.create())
                .thenReturn(mockSmtGeneratingFormulaVisitor);
    }

    @Test
    public void generateCheckSatCodeGivesCodeBeginningWithTypeDefinition() throws Z3InvalidProblemException {
        SMTCodeGenerator smtCodeGenerator = new SMTCodeGeneratorImpl(mockSmtGeneratingFormulaVisitorCreator);
        String code = smtCodeGenerator.generateCheckSatCode(new TruthFormula());
        assertThat(code).startsWith("(declare-sort Type)");
    }

    @Test
    public void generateCheckSatCodeGivesCodeIncludingPredicateDefinitions()
            throws Z3InvalidProblemException {

        List<PredicatePrototype> predicatePrototypes = new ArrayList<>();
        predicatePrototypes.add(new PredicatePrototype("Foo", Arrays.asList(Type.NAT, Type.UNKNOWN)));
        predicatePrototypes.add(new PredicatePrototype("Bar", Arrays.asList(Type.NAT, Type.NAT, Type.NAT)));

        when(mockSmtGeneratingFormulaVisitor.getPredicatePrototypes())
                .thenReturn(predicatePrototypes);

        SMTCodeGenerator smtCodeGenerator = new SMTCodeGeneratorImpl(mockSmtGeneratingFormulaVisitorCreator);
        String code = smtCodeGenerator.generateCheckSatCode(new TruthFormula());

        assertThat(code).contains("(declare-fun Foo (Int Type) Bool)");
        assertThat(code).contains("(declare-fun Bar (Int Int Int) Bool)");
    }

    @Test
    public void generateCheckSatCodeGivesCodeIncludingPropositionDefinitions()
            throws Z3InvalidProblemException {

        Set<String> propositionNames = new HashSet<>();
        propositionNames.add("P");
        propositionNames.add("Q");
        propositionNames.add("R");

        when(mockSmtGeneratingFormulaVisitor.getPropositionNames())
                .thenReturn(propositionNames);

        SMTCodeGeneratorImpl smtCodeGenerator = new SMTCodeGeneratorImpl(mockSmtGeneratingFormulaVisitorCreator);
        String code = smtCodeGenerator.generateCheckSatCode(new TruthFormula());

        assertThat(code).contains("(declare-const P Bool)");
        assertThat(code).contains("(declare-const Q Bool)");
        assertThat(code).contains("(declare-const R Bool)");
    }

    @Test
    public void generateCheckSatCodeGivesCodeIncludingConstantDefinitions()
            throws Z3InvalidProblemException {

        Map<String, Type> constantNamesToTypes = new HashMap<>();
        constantNamesToTypes.put("a", Type.UNKNOWN);
        constantNamesToTypes.put("b", Type.NAT);
        constantNamesToTypes.put("c", Type.UNKNOWN);

        when(mockSmtGeneratingFormulaVisitor.getConstantNamesToTypes())
                .thenReturn(constantNamesToTypes);

        SMTCodeGeneratorImpl smtCodeGenerator = new SMTCodeGeneratorImpl(mockSmtGeneratingFormulaVisitorCreator);
        String code = smtCodeGenerator.generateCheckSatCode(new TruthFormula());

        assertThat(code).contains("(declare-const a Type)");
        assertThat(code).contains("(declare-const b Int)");
        assertThat(code).contains("(declare-const c Type)");
    }

    @Test
    public void generateCheckSatCodeGivesCodeIncludingConstantNatGuardsBeforeCheckSat()
            throws Z3InvalidProblemException {

        Map<String, Type> constantNamesToTypes = new HashMap<>();
        constantNamesToTypes.put("a", Type.NAT);
        constantNamesToTypes.put("b", Type.UNKNOWN);
        constantNamesToTypes.put("c", Type.NAT);

        when(mockSmtGeneratingFormulaVisitor.getConstantNamesToTypes())
                .thenReturn(constantNamesToTypes);

        SMTCodeGeneratorImpl smtCodeGenerator = new SMTCodeGeneratorImpl(mockSmtGeneratingFormulaVisitorCreator);
        String code = smtCodeGenerator.generateCheckSatCode(new TruthFormula());

        assertThat(code.indexOf("(assert (>= a 0))"))
                .isPositive().isLessThan(code.indexOf("(check-sat"));

        assertThat(code.indexOf("(assert (>= c 0))"))
                .isPositive().isLessThan(code.indexOf("(check-sat"));

        assertThat(code.indexOf("(assert (>= b 0))")).isNegative();
    }

    @Test
    public void generateCheckSatCodeGivesCodeIncludingFunctionDefinitions()
            throws Z3InvalidProblemException {

        List<FunctionPrototype> functionPrototypes = new ArrayList<>();
        functionPrototypes.add(new FunctionPrototype("f", Arrays.asList(Type.NAT, Type.UNKNOWN), Type.NAT));
        functionPrototypes.add(new FunctionPrototype("g", Arrays.asList(Type.UNKNOWN, Type.NAT, Type.NAT), Type.UNKNOWN));

        when(mockSmtGeneratingFormulaVisitor.getFunctionPrototypes())
                .thenReturn(functionPrototypes);

        SMTCodeGeneratorImpl smtCodeGenerator = new SMTCodeGeneratorImpl(mockSmtGeneratingFormulaVisitorCreator);
        String code = smtCodeGenerator.generateCheckSatCode(new TruthFormula());

        assertThat(code).contains("(declare-fun f (Int Type) Int)");
        assertThat(code).contains("(declare-fun g (Type Int Int) Type)");
    }

    @Test
    public void generateCheckSatCodeGivesCodeIncludingFunctionReturnValueNatGuards() throws Z3InvalidProblemException {
        // (assert (forall ((x Int)) (>= (f x) 0))

        List<FunctionPrototype> functionPrototypes = new ArrayList<>();
        functionPrototypes.add(new FunctionPrototype("f", Arrays.asList(Type.NAT, Type.UNKNOWN, Type.NAT), Type.NAT));
        functionPrototypes.add(new FunctionPrototype("g", Arrays.asList(Type.UNKNOWN, Type.NAT, Type.NAT), Type.UNKNOWN));

        when(mockSmtGeneratingFormulaVisitor.getFunctionPrototypes())
                .thenReturn(functionPrototypes);

        SMTCodeGeneratorImpl smtCodeGenerator = new SMTCodeGeneratorImpl(mockSmtGeneratingFormulaVisitorCreator);
        String code = smtCodeGenerator.generateCheckSatCode(new TruthFormula());

        assertThat(code).contains("(assert (forall ((x0 Int)(x1 Type)(x2 Int)) (>= (f x0 x1 x2) 0)))");
    }

    @Test
    public void generateCheckSatCodeGivesCodeIncludingSingleAssert() throws Z3InvalidProblemException {
        SMTCodeGenerator smtCodeGenerator = new SMTCodeGeneratorImpl(mockSmtGeneratingFormulaVisitorCreator);
        String code = smtCodeGenerator.generateCheckSatCode(new TruthFormula());
        assertThat(code).containsOnlyOnce("(assert");
    }

    @Test
    public void generateCheckSatCodeGivesCodeIncludingAssertBeforeCheckSat() throws Z3InvalidProblemException {
        SMTCodeGenerator smtCodeGenerator = new SMTCodeGeneratorImpl(mockSmtGeneratingFormulaVisitorCreator);
        String code = smtCodeGenerator.generateCheckSatCode(new TruthFormula());
        assertThat(code.indexOf("(assert")).isLessThan(code.indexOf("(check-sat)"));
    }

    @Test
    public void generateCheckSatCodeGivesCodeIncludingSingleCheckSat() throws Z3InvalidProblemException {
        SMTCodeGenerator smtCodeGenerator = new SMTCodeGeneratorImpl(mockSmtGeneratingFormulaVisitorCreator);
        String code = smtCodeGenerator.generateCheckSatCode(new TruthFormula());
        assertThat(code).containsOnlyOnce("(check-sat)");
    }

    @Test(expected = Z3InvalidProblemException.class)
    public void generateCheckSatCodeThrowsInvalidProblemExceptionIfVisitorReportsTypeMismatch()
            throws Z3InvalidProblemException {

        when(mockSmtGeneratingFormulaVisitor.visit(any(Formula.class)))
                .thenThrow(new WrappingRuntimeException(new TypeMismatchException("Test")));

        SMTCodeGeneratorImpl smtCodeGenerator = new SMTCodeGeneratorImpl(mockSmtGeneratingFormulaVisitorCreator);
        smtCodeGenerator.generateCheckSatCode(new TruthFormula());
    }

}

package com.ipandora.core.z3;

import com.ipandora.api.predicate.formula.Formula;
import com.ipandora.api.predicate.formula.TruthFormula;
import com.ipandora.api.predicate.term.FunctionPrototype;
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
    public void generateCheckSatCodeGivesCodeIncludingPredicateDefinitionsBeforeAssert()
            throws Z3InvalidProblemException {

        List<PredicatePrototype> predicatePrototypes = new ArrayList<>();
        predicatePrototypes.add(new PredicatePrototype("Foo", Arrays.asList(Type.NAT, Type.UNKNOWN)));
        predicatePrototypes.add(new PredicatePrototype("Bar", Arrays.asList(Type.NAT, Type.NAT, Type.NAT)));

        when(mockSmtGeneratingFormulaVisitor.getPredicatePrototypes())
                .thenReturn(predicatePrototypes);

        SMTCodeGenerator smtCodeGenerator = new SMTCodeGeneratorImpl(mockSmtGeneratingFormulaVisitorCreator);
        String code = smtCodeGenerator.generateCheckSatCode(new TruthFormula());

        assertThat(code.indexOf("(declare-fun Foo (Int Type) Bool)"))
                .isPositive().isLessThan(code.indexOf("(assert"));

        assertThat(code.indexOf("(declare-fun Bar (Int Int Int) Bool)"))
                .isPositive().isLessThan(code.indexOf("(assert"));
    }

    @Test
    public void generateCheckSatCodeGivesCodeIncludingPropositionDefinitionsBeforeAssert()
            throws Z3InvalidProblemException {

        Set<String> propositionNames = new HashSet<>();
        propositionNames.add("P");
        propositionNames.add("Q");
        propositionNames.add("R");

        when(mockSmtGeneratingFormulaVisitor.getPropositionNames())
                .thenReturn(propositionNames);

        SMTCodeGeneratorImpl smtCodeGenerator = new SMTCodeGeneratorImpl(mockSmtGeneratingFormulaVisitorCreator);
        String code = smtCodeGenerator.generateCheckSatCode(new TruthFormula());

        assertThat(code.indexOf("(declare-const P Bool)"))
                .isPositive().isLessThan(code.indexOf("(assert"));

        assertThat(code.indexOf("(declare-const Q Bool)"))
                .isPositive().isLessThan(code.indexOf("(assert"));

        assertThat(code.indexOf("(declare-const R Bool)"))
                .isPositive().isLessThan(code.indexOf("(assert"));
    }

    @Test
    public void generateCheckSatCodeGivesCodeIncludingConstantDefinitionsBeforeAssert()
            throws Z3InvalidProblemException {

        Map<String, Type> constantNamesToTypes = new HashMap<>();
        constantNamesToTypes.put("a", Type.UNKNOWN);
        constantNamesToTypes.put("b", Type.NAT);
        constantNamesToTypes.put("c", Type.UNKNOWN);

        when(mockSmtGeneratingFormulaVisitor.getConstantNamesToTypes())
                .thenReturn(constantNamesToTypes);

        SMTCodeGeneratorImpl smtCodeGenerator = new SMTCodeGeneratorImpl(mockSmtGeneratingFormulaVisitorCreator);
        String code = smtCodeGenerator.generateCheckSatCode(new TruthFormula());

        assertThat(code.indexOf("(declare-const a Type)"))
                .isPositive().isLessThan(code.indexOf("(assert"));

        assertThat(code.indexOf("(declare-const b Int)"))
                .isPositive().isLessThan(code.indexOf("(assert"));

        assertThat(code.indexOf("(declare-const c Type)"))
                .isPositive().isLessThan(code.indexOf("(assert"));
    }

    @Test
    public void generateCheckSatCodeGivesCodeIncludingFunctionDefinitionsBeforeAssert()
            throws Z3InvalidProblemException {

        List<FunctionPrototype> functionPrototypes = new ArrayList<>();
        functionPrototypes.add(new FunctionPrototype("f", Arrays.asList(Type.NAT, Type.UNKNOWN), Type.NAT));
        functionPrototypes.add(new FunctionPrototype("g", Arrays.asList(Type.UNKNOWN, Type.NAT, Type.NAT), Type.UNKNOWN));

        when(mockSmtGeneratingFormulaVisitor.getFunctionPrototypes())
                .thenReturn(functionPrototypes);

        SMTCodeGeneratorImpl smtCodeGenerator = new SMTCodeGeneratorImpl(mockSmtGeneratingFormulaVisitorCreator);
        String code = smtCodeGenerator.generateCheckSatCode(new TruthFormula());

        assertThat(code.indexOf("(declare-fun f (Int Type) Int)"))
                .isPositive().isLessThan(code.indexOf("(assert"));

        assertThat(code.indexOf("(declare-fun g (Type Int Int) Type)"))
                .isPositive().isLessThan(code.indexOf("(assert"));
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

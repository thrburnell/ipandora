package com.ipandora.core.z3;

import com.ipandora.api.predicate.formula.TruthFormula;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.mockito.Mock;
import org.mockito.runners.MockitoJUnitRunner;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import static org.assertj.core.api.Assertions.assertThat;
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
    public void generateCheckSatCodeGivesCodeBeginningWithTypeDefinition() {
        SMTCodeGenerator smtCodeGenerator = new SMTCodeGeneratorImpl(mockSmtGeneratingFormulaVisitorCreator);
        String code = smtCodeGenerator.generateCheckSatCode(new TruthFormula());
        assertThat(code).startsWith("(declare-sort Type)");
    }

    @Test
    public void generateCheckSatCodeGivesCodeIncludingPredicateDefinitionsBeforeAssert() {

        Map<String, Integer> predicateNamesToArgCount = new HashMap<>();
        predicateNamesToArgCount.put("Foo", 2);
        predicateNamesToArgCount.put("Bar", 3);

        when(mockSmtGeneratingFormulaVisitor.getPredicateNamesToArgCount())
                .thenReturn(predicateNamesToArgCount);

        SMTCodeGenerator smtCodeGenerator = new SMTCodeGeneratorImpl(mockSmtGeneratingFormulaVisitorCreator);
        String code = smtCodeGenerator.generateCheckSatCode(new TruthFormula());

        assertThat(code.indexOf("(declare-fun Foo (Type Type) Bool)"))
                .isPositive().isLessThan(code.indexOf("(assert"));

        assertThat(code.indexOf("(declare-fun Bar (Type Type Type) Bool)"))
                .isPositive().isLessThan(code.indexOf("(assert"));
    }

    @Test
    public void generateCheckSatCodeGivesCodeIncludingPropositionDefinitionsBeforeAssert() {

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
    public void generateCheckSatCodeGivesCodeIncludingConstantDefinitionsBeforeAssert() {

        Set<String> constantNames = new HashSet<>();
        constantNames.add("a");
        constantNames.add("b");
        constantNames.add("c");

        when(mockSmtGeneratingFormulaVisitor.getConstantNames())
                .thenReturn(constantNames);

        SMTCodeGeneratorImpl smtCodeGenerator = new SMTCodeGeneratorImpl(mockSmtGeneratingFormulaVisitorCreator);
        String code = smtCodeGenerator.generateCheckSatCode(new TruthFormula());

        assertThat(code.indexOf("(declare-const a Type)"))
                .isPositive().isLessThan(code.indexOf("(assert"));

        assertThat(code.indexOf("(declare-const b Type)"))
                .isPositive().isLessThan(code.indexOf("(assert"));

        assertThat(code.indexOf("(declare-const c Type)"))
                .isPositive().isLessThan(code.indexOf("(assert"));
    }

    @Test
    public void generateCheckSatCodeGivesCodeIncludingFunctionDefinitionsBeforeAssert() {

        Map<String, Integer> functionNamesToArgCount = new HashMap<>();
        functionNamesToArgCount.put("f", 2);
        functionNamesToArgCount.put("g", 3);

        when(mockSmtGeneratingFormulaVisitor.getFunctionNamesToArgCount())
                .thenReturn(functionNamesToArgCount);

        SMTCodeGeneratorImpl smtCodeGenerator = new SMTCodeGeneratorImpl(mockSmtGeneratingFormulaVisitorCreator);
        String code = smtCodeGenerator.generateCheckSatCode(new TruthFormula());

        assertThat(code.indexOf("(declare-fun f (Type Type) Type)"))
                .isPositive().isLessThan(code.indexOf("(assert"));

        assertThat(code.indexOf("(declare-fun g (Type Type Type) Type)"))
                .isPositive().isLessThan(code.indexOf("(assert"));
    }

    @Test
    public void generateCheckSatCodeGivesCodeIncludingSingleAssert() {
        SMTCodeGenerator smtCodeGenerator = new SMTCodeGeneratorImpl(mockSmtGeneratingFormulaVisitorCreator);
        String code = smtCodeGenerator.generateCheckSatCode(new TruthFormula());
        assertThat(code).containsOnlyOnce("(assert");
    }

    @Test
    public void generateCheckSatCodeGivesCodeIncludingAssertBeforeCheckSat() {
        SMTCodeGenerator smtCodeGenerator = new SMTCodeGeneratorImpl(mockSmtGeneratingFormulaVisitorCreator);
        String code = smtCodeGenerator.generateCheckSatCode(new TruthFormula());
        assertThat(code.indexOf("(assert")).isLessThan(code.indexOf("(check-sat)"));
    }

    @Test
    public void generateCheckSatCodeGivesCodeIncludingSingleCheckSat() {
        SMTCodeGenerator smtCodeGenerator = new SMTCodeGeneratorImpl(mockSmtGeneratingFormulaVisitorCreator);
        String code = smtCodeGenerator.generateCheckSatCode(new TruthFormula());
        assertThat(code).containsOnlyOnce("(check-sat)");
    }

}

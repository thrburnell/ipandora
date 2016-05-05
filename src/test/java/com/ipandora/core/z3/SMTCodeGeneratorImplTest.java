package com.ipandora.core.z3;

import com.ipandora.api.predicate.formula.TruthFormula;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.mockito.Mock;
import org.mockito.runners.MockitoJUnitRunner;

import static org.assertj.core.api.Assertions.assertThat;
import static org.mockito.Mockito.when;

@RunWith(MockitoJUnitRunner.class)
public class SMTCodeGeneratorImplTest {

    @Mock
    private SMTGeneratingFormulaVisitor smtGeneratingFormulaVisitor;

    @Mock
    private SMTGeneratingFormulaVisitorCreator smtGeneratingFormulaVisitorCreator;

    @Before
    public void before() {
        when(smtGeneratingFormulaVisitorCreator.create())
                .thenReturn(smtGeneratingFormulaVisitor);
    }

    @Test
    public void generateCheckSatCodeGivesCodeBeginningWithTypeDefinition() {

        when(smtGeneratingFormulaVisitor.getTypeDefinition())
                .thenReturn("type-definition-code");

        SMTCodeGenerator smtCodeGenerator = new SMTCodeGeneratorImpl(smtGeneratingFormulaVisitorCreator);
        String code = smtCodeGenerator.generateCheckSatCode(new TruthFormula());
        assertThat(code).startsWith("type-definition-code");
    }

    @Test
    public void generateCheckSatCodeGivesCodeIncludingPredicateDefinitionsBeforeAssert() {

        when(smtGeneratingFormulaVisitor.getPredicateDefinitions())
                .thenReturn("predicate-definitions-code");

        SMTCodeGenerator smtCodeGenerator = new SMTCodeGeneratorImpl(smtGeneratingFormulaVisitorCreator);
        String code = smtCodeGenerator.generateCheckSatCode(new TruthFormula());

        assertThat(code).contains("predicate-definitions-code");
        assertThat(code.indexOf("predicate-definitions-code")).isLessThan(code.indexOf("(assert"));
    }

    @Test
    public void generateCheckSatCodeGivesCodeIncludingPropositionDefinitionsBeforeAssert() {

        when(smtGeneratingFormulaVisitor.getPropositionDefinitions())
                .thenReturn("proposition-definitions-code");

        SMTCodeGeneratorImpl smtCodeGenerator = new SMTCodeGeneratorImpl(smtGeneratingFormulaVisitorCreator);
        String code = smtCodeGenerator.generateCheckSatCode(new TruthFormula());
        assertThat(code).contains("proposition-definitions-code");
        assertThat(code.indexOf("proposition-definitions-code")).isLessThan(code.indexOf("(assert"));
    }

    @Test
    public void generateCheckSatCodeGivesCodeIncludingSingleAssert() {
        SMTCodeGenerator smtCodeGenerator = new SMTCodeGeneratorImpl(smtGeneratingFormulaVisitorCreator);
        String code = smtCodeGenerator.generateCheckSatCode(new TruthFormula());
        assertThat(code).containsOnlyOnce("(assert");
    }

    @Test
    public void generateCheckSatCodeGivesCodeIncludingAssertBeforeCheckSat() {
        SMTCodeGenerator smtCodeGenerator = new SMTCodeGeneratorImpl(smtGeneratingFormulaVisitorCreator);
        String code = smtCodeGenerator.generateCheckSatCode(new TruthFormula());
        assertThat(code.indexOf("(assert")).isLessThan(code.indexOf("(check-sat)"));
    }

    @Test
    public void generateCheckSatCodeGivesCodeIncludingSingleCheckSat() {
        SMTCodeGenerator smtCodeGenerator = new SMTCodeGeneratorImpl(smtGeneratingFormulaVisitorCreator);
        String code = smtCodeGenerator.generateCheckSatCode(new TruthFormula());
        assertThat(code).containsOnlyOnce("(check-sat)");
    }

}

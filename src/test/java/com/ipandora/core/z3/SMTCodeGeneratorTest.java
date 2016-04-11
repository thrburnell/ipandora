package com.ipandora.core.z3;

import com.ipandora.api.predicate.formula.TruthFormula;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.mockito.Mock;
import org.mockito.runners.MockitoJUnitRunner;

import static org.assertj.core.api.Assertions.assertThat;
import static org.mockito.Mockito.when;

@RunWith(MockitoJUnitRunner.class)
public class SMTCodeGeneratorTest {

    @Mock
    private SMTGeneratingFormulaVisitor smtGeneratingFormulaVisitor;

    @Test
    public void checkSatBeginsWithTypeDefinition() {

        when(smtGeneratingFormulaVisitor.getTypeDefinition())
                .thenReturn("type-definition-code");

        SMTCodeGenerator smtCodeGenerator = new SMTCodeGenerator(smtGeneratingFormulaVisitor);
        String code = smtCodeGenerator.checkSat(new TruthFormula());
        assertThat(code).startsWith("type-definition-code");
    }

    @Test
    public void checkSatIncludesPredicateDefinitionsBeforeAssert() {

        when(smtGeneratingFormulaVisitor.getPredicateDefinitions())
                .thenReturn("predicate-definitions-code");

        SMTCodeGenerator smtCodeGenerator = new SMTCodeGenerator(smtGeneratingFormulaVisitor);
        String code = smtCodeGenerator.checkSat(new TruthFormula());
        assertThat(code.indexOf("predicate-definitions-code")).isLessThan(code.indexOf("(assert"));
    }

    @Test
    public void checkSatIncludesSingleAssert() {
        SMTCodeGenerator smtCodeGenerator = new SMTCodeGenerator(smtGeneratingFormulaVisitor);
        String code = smtCodeGenerator.checkSat(new TruthFormula());
        assertThat(code).containsOnlyOnce("(assert");
    }

    @Test
    public void checkSatIncludesAssertBeforeCheckSat() {
        SMTCodeGenerator smtCodeGenerator = new SMTCodeGenerator(smtGeneratingFormulaVisitor);
        String code = smtCodeGenerator.checkSat(new TruthFormula());
        assertThat(code.indexOf("(assert")).isLessThan(code.indexOf("(check-sat)"));
    }

    @Test
    public void checkSatIncludesSingleCheckSat() {
        SMTCodeGenerator smtCodeGenerator = new SMTCodeGenerator(smtGeneratingFormulaVisitor);
        String code = smtCodeGenerator.checkSat(new TruthFormula());
        assertThat(code).containsOnlyOnce("(check-sat)");
    }

}

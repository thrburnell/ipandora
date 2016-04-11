package com.ipandora.core.z3;

import com.ipandora.api.predicate.formula.*;
import com.ipandora.api.predicate.term.Variable;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;

import static org.assertj.core.api.Assertions.assertThat;

public class SMTGeneratingFormulaVisitorImplTest {

    @Test
    public void visitAndFormulaReturnsCorrectCode() {
        // (and true (and false true))
        AndFormula andFormula = new AndFormula(new TruthFormula(),
                new AndFormula(new FalsityFormula(), new TruthFormula()));

        SMTGeneratingFormulaVisitor visitor = new SMTGeneratingFormulaVisitorImpl();
        String result = visitor.visit(andFormula);

        assertThat(result).isEqualTo("(and true (and false true))");
    }

    @Test
    public void visitOrFormulaReturnsCorrectCode() {
        // (or (or true false) false)
        OrFormula orFormula = new OrFormula(new OrFormula(new TruthFormula(), new FalsityFormula()), new FalsityFormula());

        SMTGeneratingFormulaVisitor visitor = new SMTGeneratingFormulaVisitorImpl();
        String result = visitor.visit(orFormula);

        assertThat(result).isEqualTo("(or (or true false) false)");
    }

    @Test
    public void visitForallFormulaReturnsCorrectCode() {
        // (forall ((x Type)) (Foo x))

        Variable x = new Variable("x");
        ForallFormula forallFormula = new ForallFormula(x, new PredicateFormula("Foo", Collections.singletonList(x)));

        SMTGeneratingFormulaVisitor visitor = new SMTGeneratingFormulaVisitorImpl();
        String result = visitor.visit(forallFormula);

        assertThat(result).isEqualTo("(forall ((x Type)) (Foo x))");
    }

    @Test
    public void visitExistsFormulaReturnsCorrectCode() {
        // (not (forall ((x Type)) (not (Foo x))))

        Variable x = new Variable("x");
        ExistsFormula existsFormula = new ExistsFormula(x, new PredicateFormula("Foo", Collections.singletonList(x)));

        SMTGeneratingFormulaVisitor visitor = new SMTGeneratingFormulaVisitorImpl();
        String result = visitor.visit(existsFormula);

        assertThat(result).isEqualTo("(not (forall ((x Type)) (not (Foo x))))");
    }

    @Test
    public void visitTrueFormulaReturnsCorrectCode() {
        TruthFormula truthFormula = new TruthFormula();
        SMTGeneratingFormulaVisitor visitor = new SMTGeneratingFormulaVisitorImpl();
        String result = visitor.visit(truthFormula);
        assertThat(result).isEqualTo("true");
    }

    @Test
    public void visitFalseFormulaReturnsCorrectCode() {
        FalsityFormula falsityFormula = new FalsityFormula();
        SMTGeneratingFormulaVisitor visitor = new SMTGeneratingFormulaVisitorImpl();
        String result = visitor.visit(falsityFormula);
        assertThat(result).isEqualTo("false");
    }

    @Test
    public void visitImpliesFormulaReturnsCorrectCode() {
        // (=> false true)
        ImpliesFormula impliesFormula = new ImpliesFormula(new FalsityFormula(), new TruthFormula());

        SMTGeneratingFormulaVisitor visitor = new SMTGeneratingFormulaVisitorImpl();
        String result = visitor.visit(impliesFormula);

        assertThat(result).isEqualTo("(=> false true)");
    }

    @Test
    public void visitIffFormulaReturnsCorrectCode() {
        // (= false false)
        IffFormula iffFormula = new IffFormula(new FalsityFormula(), new FalsityFormula());

        SMTGeneratingFormulaVisitor visitor = new SMTGeneratingFormulaVisitorImpl();
        String result = visitor.visit(iffFormula);

        assertThat(result).isEqualTo("(= false false)");
    }

    @Test
    public void visitNotFormulaReturnsCorrectCode() {
        // (not false)
        NotFormula notFormula = new NotFormula(new FalsityFormula());

        SMTGeneratingFormulaVisitor visitor = new SMTGeneratingFormulaVisitorImpl();
        String result = visitor.visit(notFormula);

        assertThat(result).isEqualTo("(not false)");
    }

    @Test
    public void visitPredicateFormulaReturnsCorrectCode() {
        // (Foo x y z)
        Variable x = new Variable("x");
        Variable y = new Variable("y");
        Variable z = new Variable("z");
        PredicateFormula predicateFormula = new PredicateFormula("Foo", Arrays.asList(x, y, z));

        SMTGeneratingFormulaVisitor visitor = new SMTGeneratingFormulaVisitorImpl();
        String result = visitor.visit(predicateFormula);

        assertThat(result).isEqualTo("(Foo x y z)");
    }

    @Test
    public void getPredicateDefinitionsReturnsCorrectCode() {
        // Should contain (Foo Type Type Type) and (Bar Type)

        // Foo(x, y, z) AND Bar(x)
        Variable x = new Variable("x");
        Variable y = new Variable("y");
        Variable z = new Variable("z");
        PredicateFormula fooPredicate = new PredicateFormula("Foo", Arrays.asList(x, y, z));
        PredicateFormula barPredicate = new PredicateFormula("Bar", Arrays.asList(x));

        SMTGeneratingFormulaVisitor visitor = new SMTGeneratingFormulaVisitorImpl();
        visitor.visit(new AndFormula(fooPredicate, barPredicate));
        String predicateDefinitions = visitor.getPredicateDefinitions();

        assertThat(predicateDefinitions).contains("(declare-fun Foo (Type Type Type) Bool)");
        assertThat(predicateDefinitions).contains("(declare-fun Bar (Type) Bool)");
    }

    @Test
    public void getTypeDefinitionReturnsEmptyIfNoPredicatesVisited() {
        SMTGeneratingFormulaVisitor visitor = new SMTGeneratingFormulaVisitorImpl();
        visitor.visit(new TruthFormula());
        String typeDefinition = visitor.getTypeDefinition();
        assertThat(typeDefinition).isEmpty();
    }

    @Test
    public void getTypeDefinitionReturnsCorrectCodeIfPredicatesVisited() {
        Variable x = new Variable("x");
        PredicateFormula predicateFormula = new PredicateFormula("Foo", Collections.singletonList(x));

        SMTGeneratingFormulaVisitor visitor = new SMTGeneratingFormulaVisitorImpl();
        visitor.visit(predicateFormula);
        String typeDefinition = visitor.getTypeDefinition();

        assertThat(typeDefinition).isEqualTo("(declare-sort Type)");
    }

}
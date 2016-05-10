package com.ipandora.core.z3;

import com.ipandora.api.predicate.formula.*;
import com.ipandora.api.predicate.term.Number;
import com.ipandora.api.predicate.term.Term;
import com.ipandora.api.predicate.term.Variable;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.mockito.Mock;
import org.mockito.runners.MockitoJUnitRunner;

import java.util.*;

import static org.assertj.core.api.Assertions.assertThat;
import static org.mockito.Mockito.when;

@RunWith(MockitoJUnitRunner.class)
public class SMTGeneratingFormulaVisitorImplTest {

    @Mock
    private SMTGeneratingTermVisitor mockTermVisitor;

    @Test
    public void visitAndFormulaReturnsCorrectCode() {
        // (and true (and false true))
        AndFormula andFormula = new AndFormula(new TruthFormula(),
                new AndFormula(new FalsityFormula(), new TruthFormula()));

        SMTGeneratingFormulaVisitor visitor = new SMTGeneratingFormulaVisitorImpl(mockTermVisitor);
        String result = visitor.visit(andFormula);

        assertThat(result).isEqualTo("(and true (and false true))");
    }

    @Test
    public void visitOrFormulaReturnsCorrectCode() {
        // (or (or true false) false)
        OrFormula left = new OrFormula(new TruthFormula(), new FalsityFormula());
        OrFormula orFormula = new OrFormula(left, new FalsityFormula());

        SMTGeneratingFormulaVisitor visitor = new SMTGeneratingFormulaVisitorImpl(mockTermVisitor);
        String result = visitor.visit(orFormula);

        assertThat(result).isEqualTo("(or (or true false) false)");
    }

    @Test
    public void visitForallFormulaReturnsCorrectCode() {
        // (forall ((x Type)) (Foo x))

        Variable x = new Variable("x");
        PredicateFormula predicateFormula = new PredicateFormula("Foo", Collections.<Term>singletonList(x));
        ForallFormula forallFormula = new ForallFormula(x, predicateFormula);

        SMTGeneratingTermVisitor termVisitor = new SMTGeneratingTermVisitor();
        SMTGeneratingFormulaVisitor visitor = new SMTGeneratingFormulaVisitorImpl(termVisitor);
        String result = visitor.visit(forallFormula);

        assertThat(result).isEqualTo("(forall ((x Type)) (Foo x))");
    }

    @Test
    public void visitExistsFormulaReturnsCorrectCode() {
        // (not (forall ((x Type)) (not (Foo x))))

        Variable x = new Variable("x");
        PredicateFormula predicateFormula = new PredicateFormula("Foo", Collections.<Term>singletonList(x));
        ExistsFormula existsFormula = new ExistsFormula(x, predicateFormula);

        SMTGeneratingTermVisitor termVisitor = new SMTGeneratingTermVisitor();
        SMTGeneratingFormulaVisitor visitor = new SMTGeneratingFormulaVisitorImpl(termVisitor);
        String result = visitor.visit(existsFormula);

        assertThat(result).isEqualTo("(not (forall ((x Type)) (not (Foo x))))");
    }

    @Test
    public void visitTrueFormulaReturnsCorrectCode() {
        TruthFormula truthFormula = new TruthFormula();
        SMTGeneratingFormulaVisitor visitor = new SMTGeneratingFormulaVisitorImpl(mockTermVisitor);
        String result = visitor.visit(truthFormula);
        assertThat(result).isEqualTo("true");
    }

    @Test
    public void visitFalseFormulaReturnsCorrectCode() {
        FalsityFormula falsityFormula = new FalsityFormula();
        SMTGeneratingFormulaVisitor visitor = new SMTGeneratingFormulaVisitorImpl(mockTermVisitor);
        String result = visitor.visit(falsityFormula);
        assertThat(result).isEqualTo("false");
    }

    @Test
    public void visitImpliesFormulaReturnsCorrectCode() {
        // (=> false true)
        ImpliesFormula impliesFormula = new ImpliesFormula(new FalsityFormula(), new TruthFormula());

        SMTGeneratingFormulaVisitor visitor = new SMTGeneratingFormulaVisitorImpl(mockTermVisitor);
        String result = visitor.visit(impliesFormula);

        assertThat(result).isEqualTo("(=> false true)");
    }

    @Test
    public void visitIffFormulaReturnsCorrectCode() {
        // (= false false)
        IffFormula iffFormula = new IffFormula(new FalsityFormula(), new FalsityFormula());

        SMTGeneratingFormulaVisitor visitor = new SMTGeneratingFormulaVisitorImpl(mockTermVisitor);
        String result = visitor.visit(iffFormula);

        assertThat(result).isEqualTo("(= false false)");
    }

    @Test
    public void visitNotFormulaReturnsCorrectCode() {
        // (not false)
        NotFormula notFormula = new NotFormula(new FalsityFormula());

        SMTGeneratingFormulaVisitor visitor = new SMTGeneratingFormulaVisitorImpl(mockTermVisitor);
        String result = visitor.visit(notFormula);

        assertThat(result).isEqualTo("(not false)");
    }

    @Test
    public void visitPropositionFormulaReturnsCorrectCode() {
        // P
        PropositionFormula p = new PropositionFormula("P");

        SMTGeneratingFormulaVisitorImpl visitor = new SMTGeneratingFormulaVisitorImpl(mockTermVisitor);
        String result = visitor.visit(p);

        assertThat(result).isEqualTo("P");
    }

    @Test
    public void visitPredicateFormulaReturnsCorrectCode() {
        // (Foo x y z)
        Variable x = new Variable("x");
        Variable y = new Variable("y");
        Variable z = new Variable("z");
        PredicateFormula predicateFormula = new PredicateFormula("Foo", Arrays.<Term>asList(x, y, z));

        SMTGeneratingTermVisitor termVisitor = new SMTGeneratingTermVisitor();
        SMTGeneratingFormulaVisitor visitor = new SMTGeneratingFormulaVisitorImpl(termVisitor);
        String result = visitor.visit(predicateFormula);

        assertThat(result).isEqualTo("(Foo x y z)");
    }

    @Test
    public void visitEqualToFormulaReturnsCorrectCode() {
        EqualToFormula equalToFormula = new EqualToFormula(Variable.withTypeNat("x"), new Number(3));

        SMTGeneratingTermVisitor termVisitor = new SMTGeneratingTermVisitor();
        SMTGeneratingFormulaVisitorImpl visitor = new SMTGeneratingFormulaVisitorImpl(termVisitor);
        String result = visitor.visit(equalToFormula);

        assertThat(result).isEqualTo("(= x 3)");
    }

    @Test
    public void visitGreaterThanFormulaReturnsCorrectCode() {
        GreaterThanFormula greaterThanFormula = new GreaterThanFormula(Variable.withTypeNat("x"), new Number(2));

        SMTGeneratingTermVisitor termVisitor = new SMTGeneratingTermVisitor();
        SMTGeneratingFormulaVisitorImpl visitor = new SMTGeneratingFormulaVisitorImpl(termVisitor);
        String result = visitor.visit(greaterThanFormula);

        assertThat(result).isEqualTo("(> x 2)");
    }

    @Test
    public void visitLessThanFormulaReturnsCorrectCode() {
        LessThanFormula lessThanFormula = new LessThanFormula(Variable.withTypeNat("x"), new Number(13));

        SMTGeneratingTermVisitor termVisitor = new SMTGeneratingTermVisitor();
        SMTGeneratingFormulaVisitorImpl visitor = new SMTGeneratingFormulaVisitorImpl(termVisitor);
        String result = visitor.visit(lessThanFormula);

        assertThat(result).isEqualTo("(< x 13)");
    }

    @Test
    public void visitGreaterThanEqualFormulaReturnsCorrectCode() {
        GreaterThanEqualFormula greaterThanEqualFormula = new GreaterThanEqualFormula(Variable.withTypeNat("x"), new Number(3));

        SMTGeneratingTermVisitor termVisitor = new SMTGeneratingTermVisitor();
        SMTGeneratingFormulaVisitorImpl visitor = new SMTGeneratingFormulaVisitorImpl(termVisitor);
        String result = visitor.visit(greaterThanEqualFormula);

        assertThat(result).isEqualTo("(>= x 3)");
    }

    @Test
    public void visitLessThanEqualFormulaReturnsCorrectCode() {
        LessThanEqualFormula lessThanEqualFormula = new LessThanEqualFormula(Variable.withTypeNat("z"), Variable.withTypeNat("m"));

        SMTGeneratingTermVisitor termVisitor = new SMTGeneratingTermVisitor();
        SMTGeneratingFormulaVisitorImpl visitor = new SMTGeneratingFormulaVisitorImpl(termVisitor);
        String result = visitor.visit(lessThanEqualFormula);

        assertThat(result).isEqualTo("(<= z m)");
    }

    @Test
    public void getPredicateDefinitionsReturnsCorrectCode() {
        // Should contain (Foo Type Type Type) and (Bar Type)

        // Foo(x, y, z) AND Bar(x)
        Variable x = new Variable("x");
        Variable y = new Variable("y");
        Variable z = new Variable("z");
        PredicateFormula fooPredicate = new PredicateFormula("Foo", Arrays.<Term>asList(x, y, z));
        PredicateFormula barPredicate = new PredicateFormula("Bar", Arrays.<Term>asList(x));

        SMTGeneratingTermVisitor termVisitor = new SMTGeneratingTermVisitor();
        SMTGeneratingFormulaVisitor visitor = new SMTGeneratingFormulaVisitorImpl(termVisitor);
        visitor.visit(new AndFormula(fooPredicate, barPredicate));
        String predicateDefinitions = visitor.getPredicateDefinitions();

        assertThat(predicateDefinitions).contains("(declare-fun Foo (Type Type Type) Bool)");
        assertThat(predicateDefinitions).contains("(declare-fun Bar (Type) Bool)");
    }

    @Test
    public void getTypeDefinitionReturnsEmptyIfNoPredicatesVisited() {
        SMTGeneratingFormulaVisitor visitor = new SMTGeneratingFormulaVisitorImpl(mockTermVisitor);
        visitor.visit(new TruthFormula());
        String typeDefinition = visitor.getTypeDefinition();
        assertThat(typeDefinition).isEmpty();
    }

    @Test
    public void getTypeDefinitionReturnsCorrectCodeIfPredicatesVisited() {
        Variable x = new Variable("x");
        PredicateFormula predicateFormula = new PredicateFormula("Foo", Collections.<Term>singletonList(x));

        SMTGeneratingTermVisitor termVisitor = new SMTGeneratingTermVisitor();
        SMTGeneratingFormulaVisitor visitor = new SMTGeneratingFormulaVisitorImpl(termVisitor);
        visitor.visit(predicateFormula);
        String typeDefinition = visitor.getTypeDefinition();

        assertThat(typeDefinition).isEqualTo("(declare-sort Type)");
    }

    @Test
    public void getPropositionDefinitionsReturnsCorrectCode() {

        // P AND Q AND R
        PropositionFormula p = new PropositionFormula("P");
        PropositionFormula q = new PropositionFormula("Q");
        PropositionFormula r = new PropositionFormula("R");
        AndFormula andFormula = new AndFormula(p, new OrFormula(q, r));

        SMTGeneratingFormulaVisitorImpl visitor = new SMTGeneratingFormulaVisitorImpl(mockTermVisitor);
        visitor.visit(andFormula);
        String propositionDefinitions = visitor.getPropositionDefinitions();

        assertThat(propositionDefinitions).contains("(declare-const P Bool)");
        assertThat(propositionDefinitions).contains("(declare-const Q Bool)");
        assertThat(propositionDefinitions).contains("(declare-const R Bool)");
    }

    @Test
    public void getConstantDefinitionsReturnsCorrectCode() {

        when(mockTermVisitor.getConstants())
                .thenReturn(new HashSet<>(Arrays.asList("x", "z", "q")));

        SMTGeneratingFormulaVisitorImpl visitor = new SMTGeneratingFormulaVisitorImpl(mockTermVisitor);
        visitor.visit(new TruthFormula());
        String constantDefinitions = visitor.getConstantDefinitions();

        assertThat(constantDefinitions).contains("(declare-const x Type)");
        assertThat(constantDefinitions).contains("(declare-const z Type)");
        assertThat(constantDefinitions).contains("(declare-const q Type)");
    }

    @Test
    public void getFunctionDefinitionsReturnsCorrectCode() {

        Map<String, Integer> functions = new HashMap<>();
        functions.put("f", 3);
        functions.put("g", 2);

        when(mockTermVisitor.getFunctions()).thenReturn(functions);

        SMTGeneratingFormulaVisitorImpl visitor = new SMTGeneratingFormulaVisitorImpl(mockTermVisitor);
        visitor.visit(new TruthFormula());
        String functionDefinitions = visitor.getFunctionDefinitions();

        assertThat(functionDefinitions).contains("(declare-fun f (Type Type Type) Type)");
        assertThat(functionDefinitions).contains("(declare-fun g (Type Type) Type)");
    }

}

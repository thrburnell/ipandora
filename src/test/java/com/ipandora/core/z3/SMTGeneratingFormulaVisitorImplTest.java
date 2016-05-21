package com.ipandora.core.z3;

import com.ipandora.api.predicate.formula.*;
import com.ipandora.api.predicate.term.FunctionPrototype;
import com.ipandora.api.predicate.formula.PredicatePrototype;
import com.ipandora.api.predicate.term.*;
import com.ipandora.api.predicate.term.Number;
import com.ipandora.core.util.WrappingRuntimeException;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.mockito.Mock;
import org.mockito.runners.MockitoJUnitRunner;

import java.util.*;

import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.core.api.Assertions.fail;
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
        // (forall ((x Int) (y Type) (z Int)) (Foo x))

        Variable x = Variable.withTypeNat("x");
        Variable y = new Variable("y");
        Variable z = Variable.withTypeNat("z");
        PredicateFormula predicateFormula = new PredicateFormula("Foo", Collections.<Term>singletonList(x));
        ForallFormula forallFormula = new ForallFormula(predicateFormula, x, y, z);

        SMTGeneratingTermVisitor termVisitor = new SMTGeneratingTermVisitor();
        SMTGeneratingFormulaVisitor visitor = new SMTGeneratingFormulaVisitorImpl(termVisitor);
        String result = visitor.visit(forallFormula);

        assertThat(result).isEqualTo("(forall ((x Int)(z Int)(y Type)) (Foo x))");
    }

    @Test
    public void visitExistsFormulaReturnsCorrectCode() {
        // (not (forall ((x Type)) (not (Foo x))))

        Variable x = new Variable("x");
        Variable y = new Variable("y");
        Variable z = new Variable("z");
        PredicateFormula predicateFormula = new PredicateFormula("Foo", Collections.<Term>singletonList(x));
        ExistsFormula existsFormula = new ExistsFormula(predicateFormula, x, y, z);

        SMTGeneratingTermVisitor termVisitor = new SMTGeneratingTermVisitor();
        SMTGeneratingFormulaVisitor visitor = new SMTGeneratingFormulaVisitorImpl(termVisitor);
        String result = visitor.visit(existsFormula);

        assertThat(result).isEqualTo("(not (forall ((x Type)(y Type)(z Type)) (not (Foo x))))");
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

    @Test(expected = TypeMismatchException.class)
    public void visitPredicateFormulaThrowsIfPredicateUsedMultipleTimesWithDifferentArgTypes() throws Exception {
        SMTGeneratingTermVisitor termVisitor = new SMTGeneratingTermVisitor();
        SMTGeneratingFormulaVisitor visitor = new SMTGeneratingFormulaVisitorImpl(termVisitor);

        visitor.visit(new PredicateFormula("Foo", Arrays.<Term>asList(Variable.withTypeNat("x"), new Variable("y"))));

        try {
            visitor.visit(new PredicateFormula("Foo", Arrays.<Term>asList(new Variable("x"), Variable.withTypeNat("y"))));
            fail("WrappingRuntimeException should have been thrown!");
        } catch (WrappingRuntimeException wre) {
            throw wre.getWrappedException();
        }
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
    public void getPredicatePrototypesReturnsCorrectList() {
        // Should contain (Foo Int Type Type) and (Bar Int)

        // Foo(x, y, z) AND Bar(x)
        Variable x = Variable.withTypeNat("x");
        Variable y = new Variable("y");
        Variable z = new Variable("z");
        PredicateFormula fooPredicate = new PredicateFormula("Foo", Arrays.<Term>asList(x, y, z));
        PredicateFormula barPredicate = new PredicateFormula("Bar", Arrays.<Term>asList(x));

        SMTGeneratingTermVisitor termVisitor = new SMTGeneratingTermVisitor();
        SMTGeneratingFormulaVisitor visitor = new SMTGeneratingFormulaVisitorImpl(termVisitor);
        visitor.visit(new AndFormula(fooPredicate, barPredicate));

        List<PredicatePrototype> predicates =  visitor.getPredicatePrototypes();

        assertThat(predicates).hasSize(2);
        assertThat(predicates).contains(new PredicatePrototype("Foo", Arrays.asList(Type.NAT, Type.UNKNOWN, Type.UNKNOWN)));
        assertThat(predicates).contains(new PredicatePrototype("Bar", Collections.singletonList(Type.NAT)));
    }

    @Test
    public void getPropositionNamesReturnsCorrectSet() {

        // P AND Q AND R
        PropositionFormula p = new PropositionFormula("P");
        PropositionFormula q = new PropositionFormula("Q");
        PropositionFormula r = new PropositionFormula("R");
        AndFormula andFormula = new AndFormula(p, new OrFormula(q, r));

        SMTGeneratingFormulaVisitorImpl visitor = new SMTGeneratingFormulaVisitorImpl(mockTermVisitor);
        visitor.visit(andFormula);
        Set<String> propositionDefinitions = visitor.getPropositionNames();

        assertThat(propositionDefinitions).containsExactlyInAnyOrder("P", "Q", "R");
    }

    @Test
    public void getConstantNamesToTypesReturnsResultFromTermVisitor() {

        Map<String, Type> constNamesToTypes = new HashMap<>();
        constNamesToTypes.put("x", Type.UNKNOWN);
        constNamesToTypes.put("y", Type.NAT);

        when(mockTermVisitor.getConstantNamesToTypes()).thenReturn(constNamesToTypes);

        SMTGeneratingFormulaVisitorImpl visitor = new SMTGeneratingFormulaVisitorImpl(mockTermVisitor);
        visitor.visit(new TruthFormula());
        Map<String, Type> constantDefinitions = visitor.getConstantNamesToTypes();

        assertThat(constantDefinitions).isEqualTo(constNamesToTypes);
    }

    @Test
    public void getFunctionNamesToArgCountReturnsResultFromTermVisitor() {

        List<FunctionPrototype> prototypes = new ArrayList<>();
        prototypes.add(new FunctionPrototype("f", Arrays.asList(Type.UNKNOWN, Type.NAT, Type.NAT), Type.UNKNOWN));
        prototypes.add(new FunctionPrototype("g", Arrays.asList(Type.NAT, Type.UNKNOWN), Type.NAT));

        when(mockTermVisitor.getFunctionPrototypes()).thenReturn(prototypes);

        SMTGeneratingFormulaVisitorImpl visitor = new SMTGeneratingFormulaVisitorImpl(mockTermVisitor);
        visitor.visit(new TruthFormula());
        List<FunctionPrototype> functionDefinitions = visitor.getFunctionPrototypes();

        assertThat(functionDefinitions).isEqualTo(prototypes);
    }

}

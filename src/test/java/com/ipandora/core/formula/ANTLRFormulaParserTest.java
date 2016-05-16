package com.ipandora.core.formula;

import com.ipandora.api.predicate.formula.*;
import com.ipandora.api.predicate.term.*;
import com.ipandora.api.predicate.term.Number;
import com.ipandora.core.term.SymbolTableCreator;
import com.ipandora.core.term.TermBuildingVisitor;
import com.ipandora.core.term.TermTypeChecker;
import org.junit.Before;
import org.junit.Test;
import org.mockito.Mockito;

import java.util.Arrays;
import java.util.Collections;

import static org.assertj.core.api.Assertions.assertThat;
import static org.mockito.Mockito.verify;

public class ANTLRFormulaParserTest {

    private ANTLRFormulaParser parser;

    @Before
    public void before() {
        SymbolTableCreator symbolTableCreator = new SymbolTableCreator();
        FormulaBuildingVisitor visitor = new FormulaBuildingVisitor(new TermBuildingVisitor(symbolTableCreator));
        TypeCheckAnalyser typeCheckAnalyser = new TypeCheckAnalyser(new TermTypeChecker());
        parser = new ANTLRFormulaParser(visitor, typeCheckAnalyser);
    }

    @Test
    public void fromStringPropositionalVariable() throws FormulaParsingException {
        Formula formula = parser.fromString("p");
        PropositionFormula expected = new PropositionFormula("p");
        assertThat(formula).isEqualTo(expected);
    }

    @Test
    public void fromStringPredicateWithSingleArgument() throws FormulaParsingException {
        Formula formula = parser.fromString("Foo(x)");
        PredicateFormula expected = new PredicateFormula("Foo", Collections.<Term>singletonList(new Constant("x")));
        assertThat(formula).isEqualTo(expected);
    }

    @Test
    public void fromStringPredicateWithMultipleArguments() throws FormulaParsingException {
        Formula formula = parser.fromString("Foo(?x, y, 13)");
        PredicateFormula expected = new PredicateFormula("Foo",
                Arrays.asList(new Variable("?x"), new Constant("y"), new Number(13)));

        assertThat(formula).isEqualTo(expected);
    }

    @Test
    public void fromStringPredicateWithArithmeticArgment() throws FormulaParsingException {
        Formula formula = parser.fromString("Foo(1 + 3 * 4 ^ 2)");

        Power power = new Power(new Number(4), 2);
        Multiplication multiplication = new Multiplication(new Number(3), power);
        Addition addition = new Addition(new Number(1), multiplication);
        PredicateFormula expected = new PredicateFormula("Foo", Collections.<Term>singletonList(addition));

        assertThat(formula).isEqualTo(expected);
    }

    @Test
    public void fromStringForallWithNoDomain() throws FormulaParsingException {
        Formula formula = parser.fromString("\\FORALL ?x Foo(?x)");
        ForallFormula expected = new ForallFormula(new Variable("?x"),
                new PredicateFormula("Foo", Collections.<Term>singletonList(new Variable("?x"))));

        assertThat(formula).isEqualTo(expected);
    }

    @Test
    public void fromStringForallWithDomain() throws FormulaParsingException {
        Formula formula = parser.fromString("\\FORALL ?x in Nat Foo(?x)");
        ForallFormula expected = new ForallFormula(Variable.withTypeNat("?x"),
                new PredicateFormula("Foo", Collections.<Term>singletonList(Variable.withTypeNat("?x"))));

        assertThat(formula).isEqualTo(expected);
    }

    @Test
    public void fromStringExistsWithNoDomain() throws FormulaParsingException {
        Formula formula = parser.fromString("\\EXISTS ?x Foo(?x)");
        ExistsFormula expected = new ExistsFormula(new Variable("?x"),
                new PredicateFormula("Foo", Collections.<Term>singletonList(new Variable("?x"))));

        assertThat(formula).isEqualTo(expected);
    }

    @Test
    public void fromStringExistsWithDomain() throws FormulaParsingException {
        Formula formula = parser.fromString("\\EXISTS ?x in Nat Foo(?x)");
        ExistsFormula expected = new ExistsFormula(Variable.withTypeNat("?x"),
                new PredicateFormula("Foo", Collections.<Term>singletonList(Variable.withTypeNat("?x"))));

        assertThat(formula).isEqualTo(expected);
    }

    @Test
    public void fromStringNestedQuantifiersWithOverridingDomains() throws FormulaParsingException {
        Formula formula = parser.fromString("\\FORALL ?x \\FORALL ?x in Nat Foo(?x)");

        Variable xNat = Variable.withTypeNat("?x");
        Variable xUnknown = new Variable("?x");

        ForallFormula nested = new ForallFormula(xNat,
                new PredicateFormula("Foo", Collections.<Term>singletonList(xNat)));

        ForallFormula expected = new ForallFormula(xUnknown, nested);

        assertThat(formula).isEqualTo(expected);
    }

    @Test
    public void fromStringNestedQuantifiersWithOverridingDomains2() throws FormulaParsingException {
        Formula formula = parser.fromString("\\FORALL ?x in Nat \\FORALL ?x Foo(?x)");

        Variable xNat = Variable.withTypeNat("?x");
        Variable xUnknown = new Variable("?x");

        ForallFormula nested = new ForallFormula(xUnknown,
                new PredicateFormula("Foo", Collections.<Term>singletonList(xUnknown)));

        ForallFormula expected = new ForallFormula(xNat, nested);

        assertThat(formula).isEqualTo(expected);
    }

    @Test
    public void fromStringBooleanExpression() throws FormulaParsingException {
        Formula formula = parser.fromString("1 + 3 > 2 * 1");

        Addition addition = new Addition(new Number(1), new Number(3));
        Multiplication multiplication = new Multiplication(new Number(2), new Number(1));
        GreaterThanFormula expected = new GreaterThanFormula(addition, multiplication);

        assertThat(formula).isEqualTo(expected);
    }

    @Test
    public void fromStringSimplePredicateWithRedundantWrappingParenthesis() throws FormulaParsingException {
        Formula formula = parser.fromString("((((((Foo(?x)))))))");
        PredicateFormula expected = new PredicateFormula("Foo", Collections.<Term>singletonList(new Variable("?x")));
        assertThat(formula).isEqualTo(expected);
    }

    @Test
    public void fromStringNegatedPredicate() throws FormulaParsingException {
        Formula formula = parser.fromString("!Foo(?x)");
        PredicateFormula nested = new PredicateFormula("Foo", Collections.<Term>singletonList(new Variable("?x")));
        NotFormula expected = new NotFormula(nested);
        assertThat(formula).isEqualTo(expected);
    }

    @Test
    public void fromStringConjunctionOfPredicates() throws FormulaParsingException {
        Formula formula = parser.fromString("Foo(?x) & Bar(?y)");
        PredicateFormula foo = new PredicateFormula("Foo", Collections.<Term>singletonList(new Variable("?x")));
        PredicateFormula bar = new PredicateFormula("Bar", Collections.<Term>singletonList(new Variable("?y")));
        AndFormula expected = new AndFormula(foo, bar);
        assertThat(formula).isEqualTo(expected);
    }

    @Test
    public void fromStringDisjunctionOfPredicates() throws FormulaParsingException {
        Formula formula = parser.fromString("Foo(?x) | Bar(?y)");
        PredicateFormula foo = new PredicateFormula("Foo", Collections.<Term>singletonList(new Variable("?x")));
        PredicateFormula bar = new PredicateFormula("Bar", Collections.<Term>singletonList(new Variable("?y")));
        OrFormula expected = new OrFormula(foo, bar);
        assertThat(formula).isEqualTo(expected);
    }

    @Test
    public void fromStringImpliesOfPredicates() throws FormulaParsingException {
        Formula formula = parser.fromString("Foo(?x) -> Bar(?y)");
        PredicateFormula foo = new PredicateFormula("Foo", Collections.<Term>singletonList(new Variable("?x")));
        PredicateFormula bar = new PredicateFormula("Bar", Collections.<Term>singletonList(new Variable("?y")));
        ImpliesFormula expected = new ImpliesFormula(foo, bar);
        assertThat(formula).isEqualTo(expected);
    }

    @Test
    public void fromStringIffOfPredicates() throws FormulaParsingException {
        Formula formula = parser.fromString("Foo(?x) <-> Bar(?y)");
        PredicateFormula foo = new PredicateFormula("Foo", Collections.<Term>singletonList(new Variable("?x")));
        PredicateFormula bar = new PredicateFormula("Bar", Collections.<Term>singletonList(new Variable("?y")));
        IffFormula expected = new IffFormula(foo, bar);
        assertThat(formula).isEqualTo(expected);
    }

    @Test
    public void fromStringExplicitlyParenthesisedConnectedPredicates() throws FormulaParsingException {
        Formula formula = parser.fromString("!(P & ((Q | R) -> (S <-> T)))");

        PropositionFormula p = new PropositionFormula("P");
        PropositionFormula q = new PropositionFormula("Q");
        PropositionFormula r = new PropositionFormula("R");
        PropositionFormula s = new PropositionFormula("S");
        PropositionFormula t = new PropositionFormula("T");

        IffFormula iff = new IffFormula(s, t);
        OrFormula or = new OrFormula(q, r);
        ImpliesFormula implies = new ImpliesFormula(or, iff);
        AndFormula and = new AndFormula(p, implies);
        NotFormula expected = new NotFormula(and);

        assertThat(formula).isEqualTo(expected);
    }

    @Test
    public void fromStringShouldInferImplicitBracketing() throws FormulaParsingException {
        Formula formula = parser.fromString("P -> Q & R <-> S | !T");

        PropositionFormula p = new PropositionFormula("P");
        PropositionFormula q = new PropositionFormula("Q");
        PropositionFormula r = new PropositionFormula("R");
        PropositionFormula s = new PropositionFormula("S");
        PropositionFormula t = new PropositionFormula("T");

        NotFormula not = new NotFormula(t);
        AndFormula and = new AndFormula(q, r);
        OrFormula or = new OrFormula(s, not);
        ImpliesFormula implies = new ImpliesFormula(p, and);
        IffFormula expected = new IffFormula(implies, or);

        assertThat(formula).isEqualTo(expected);
    }

    @Test(expected = FormulaParsingException.class)
    public void fromStringShouldThrowIfUntypedVariableUsedInArithmeticExpression() throws FormulaParsingException {
        parser.fromString("Foo(?x + 2)");
    }

    @Test(expected = FormulaParsingException.class)
    public void fromStringShouldThrowIfUntypedVariableUsedInBooleanExpression() throws FormulaParsingException {
        parser.fromString("?x > 2");
    }

    @Test
    public void fromStringShouldTypeCheckFormula() throws FormulaParsingException {
        SymbolTableCreator symbolTableCreator = new SymbolTableCreator();
        FormulaBuildingVisitor visitor = new FormulaBuildingVisitor(new TermBuildingVisitor(symbolTableCreator));
        TypeCheckAnalyser mockTypeCheckAnalyser = Mockito.mock(TypeCheckAnalyser.class);
        parser = new ANTLRFormulaParser(visitor, mockTypeCheckAnalyser);

        Formula formula = parser.fromString("\\FORALL ?x in Nat ?x > 2");

        verify(mockTypeCheckAnalyser).analyse(formula);
    }

}

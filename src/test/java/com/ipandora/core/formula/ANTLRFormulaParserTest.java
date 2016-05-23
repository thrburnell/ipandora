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
        FormulaBuildingVisitor visitor = new FormulaBuildingVisitor(
                new TermBuildingVisitor(symbolTableCreator.create(), symbolTableCreator));
        FormulaTypeChecker formulaTypeChecker = new FormulaTypeChecker(new TermTypeChecker());
        parser = new ANTLRFormulaParser(visitor, formulaTypeChecker);
    }

    @Test
    public void fromStringTruth() throws FormulaParsingException {
        Formula formula = parser.fromStringWithTypeChecking("\\TRUTH");
        TruthFormula expected = new TruthFormula();
        assertThat(formula).isEqualTo(expected);
    }

    @Test
    public void fromStringFalsity() throws FormulaParsingException {
        Formula formula = parser.fromStringWithTypeChecking("\\FALSITY");
        FalsityFormula expected = new FalsityFormula();
        assertThat(formula).isEqualTo(expected);
    }

    @Test
    public void fromStringPropositionalVariable() throws FormulaParsingException {
        Formula formula = parser.fromStringWithTypeChecking("p");
        PropositionFormula expected = new PropositionFormula("p");
        assertThat(formula).isEqualTo(expected);
    }

    @Test
    public void fromStringPredicateWithSingleArgument() throws FormulaParsingException {
        Formula formula = parser.fromStringWithTypeChecking("Foo(x)");
        PredicateFormula expected = new PredicateFormula("Foo", Collections.<Term>singletonList(new Constant("x")));
        assertThat(formula).isEqualTo(expected);
    }

    @Test
    public void fromStringPredicateWithMultipleArguments() throws FormulaParsingException {
        Formula formula = parser.fromStringWithTypeChecking("Foo(x, y, 13)");
        PredicateFormula expected = new PredicateFormula("Foo",
                Arrays.<Term>asList(new Constant("x"), new Constant("y"), new Number(13)));

        assertThat(formula).isEqualTo(expected);
    }

    @Test
    public void fromStringPredicateWithArithmeticArgment() throws FormulaParsingException {
        Formula formula = parser.fromStringWithTypeChecking("Foo(1 + 3 * 4 ^ 2)");

        Power power = new Power(new Number(4), 2);
        Multiplication multiplication = new Multiplication(new Number(3), power);
        Addition addition = new Addition(new Number(1), multiplication);
        PredicateFormula expected = new PredicateFormula("Foo", Collections.<Term>singletonList(addition));

        assertThat(formula).isEqualTo(expected);
    }

    @Test
    public void fromStringForallWithNoDomain() throws FormulaParsingException {
        Formula formula = parser.fromStringWithTypeChecking("\\FORALL x. Foo(x)");
        ForallFormula expected = new ForallFormula(new Variable("x"),
                new PredicateFormula("Foo", Collections.<Term>singletonList(new Variable("x"))));

        assertThat(formula).isEqualTo(expected);
    }

    @Test
    public void fromStringForallWithDomain() throws FormulaParsingException {
        Formula formula = parser.fromStringWithTypeChecking("\\FORALL x in Nat. Foo(x)");
        ForallFormula expected = new ForallFormula(Variable.withTypeNat("x"),
                new PredicateFormula("Foo", Collections.<Term>singletonList(Variable.withTypeNat("x"))));

        assertThat(formula).isEqualTo(expected);
    }

    @Test
    public void fromStringForallWithManyVarsDifferingDomains() throws FormulaParsingException {
        Formula formula = parser.fromStringWithTypeChecking("\\FORALL x, y in Nat, z. (x + y = 0 & Foo(z))");

        Variable x = Variable.withTypeNat("x");
        Variable y = Variable.withTypeNat("y");
        Variable z = new Variable("z");
        ForallFormula expected = new ForallFormula(new AndFormula(
                new EqualToFormula(new Addition(x, y), new Number(0)),
                new PredicateFormula("Foo", Collections.<Term>singletonList(z))), x, y, z);

        assertThat(formula).isEqualTo(expected);
    }

    @Test
    public void fromStringExistsWithNoDomain() throws FormulaParsingException {
        Formula formula = parser.fromStringWithTypeChecking("\\EXISTS x. Foo(x)");
        ExistsFormula expected = new ExistsFormula(new Variable("x"),
                new PredicateFormula("Foo", Collections.<Term>singletonList(new Variable("x"))));

        assertThat(formula).isEqualTo(expected);
    }

    @Test
    public void fromStringExistsWithDomain() throws FormulaParsingException {
        Formula formula = parser.fromStringWithTypeChecking("\\EXISTS x in Nat. Foo(x)");
        ExistsFormula expected = new ExistsFormula(Variable.withTypeNat("x"),
                new PredicateFormula("Foo", Collections.<Term>singletonList(Variable.withTypeNat("x"))));

        assertThat(formula).isEqualTo(expected);
    }

    @Test
    public void fromStringNestedQuantifiersWithOverridingDomains() throws FormulaParsingException {
        Formula formula = parser.fromStringWithTypeChecking("\\FORALL x. \\FORALL x in Nat. Foo(x)");

        Variable xNat = Variable.withTypeNat("x");
        Variable xUnknown = new Variable("x");

        ForallFormula nested = new ForallFormula(xNat,
                new PredicateFormula("Foo", Collections.<Term>singletonList(xNat)));

        ForallFormula expected = new ForallFormula(xUnknown, nested);

        assertThat(formula).isEqualTo(expected);
    }

    @Test
    public void fromStringNestedQuantifiersWithOverridingDomains2() throws FormulaParsingException {
        Formula formula = parser.fromStringWithTypeChecking("\\FORALL x in Nat. \\FORALL x. Foo(x)");

        Variable xNat = Variable.withTypeNat("x");
        Variable xUnknown = new Variable("x");

        ForallFormula nested = new ForallFormula(xUnknown,
                new PredicateFormula("Foo", Collections.<Term>singletonList(xUnknown)));

        ForallFormula expected = new ForallFormula(xNat, nested);

        assertThat(formula).isEqualTo(expected);
    }

    @Test
    public void fromStringBooleanExpression() throws FormulaParsingException {
        Formula formula = parser.fromStringWithTypeChecking("1 + 3 > 2 * 1");

        Addition addition = new Addition(new Number(1), new Number(3));
        Multiplication multiplication = new Multiplication(new Number(2), new Number(1));
        GreaterThanFormula expected = new GreaterThanFormula(addition, multiplication);

        assertThat(formula).isEqualTo(expected);
    }

    @Test
    public void fromStringSimplePredicateWithRedundantWrappingParenthesis() throws FormulaParsingException {
        Formula formula = parser.fromStringWithTypeChecking("((((((Foo(x)))))))");
        PredicateFormula expected = new PredicateFormula("Foo", Collections.<Term>singletonList(new Constant("x")));
        assertThat(formula).isEqualTo(expected);
    }

    @Test
    public void fromStringNegatedPredicate() throws FormulaParsingException {
        Formula formula = parser.fromStringWithTypeChecking("!Foo(x)");
        PredicateFormula nested = new PredicateFormula("Foo", Collections.<Term>singletonList(new Constant("x")));
        NotFormula expected = new NotFormula(nested);
        assertThat(formula).isEqualTo(expected);
    }

    @Test
    public void fromStringConjunctionOfPredicates() throws FormulaParsingException {
        Formula formula = parser.fromStringWithTypeChecking("Foo(x) & Bar(y)");
        PredicateFormula foo = new PredicateFormula("Foo", Collections.<Term>singletonList(new Constant("x")));
        PredicateFormula bar = new PredicateFormula("Bar", Collections.<Term>singletonList(new Constant("y")));
        AndFormula expected = new AndFormula(foo, bar);
        assertThat(formula).isEqualTo(expected);
    }

    @Test
    public void fromStringDisjunctionOfPredicates() throws FormulaParsingException {
        Formula formula = parser.fromStringWithTypeChecking("Foo(x) | Bar(y)");
        PredicateFormula foo = new PredicateFormula("Foo", Collections.<Term>singletonList(new Constant("x")));
        PredicateFormula bar = new PredicateFormula("Bar", Collections.<Term>singletonList(new Constant("y")));
        OrFormula expected = new OrFormula(foo, bar);
        assertThat(formula).isEqualTo(expected);
    }

    @Test
    public void fromStringImpliesOfPredicates() throws FormulaParsingException {
        Formula formula = parser.fromStringWithTypeChecking("Foo(x) -> Bar(y)");
        PredicateFormula foo = new PredicateFormula("Foo", Collections.<Term>singletonList(new Constant("x")));
        PredicateFormula bar = new PredicateFormula("Bar", Collections.<Term>singletonList(new Constant("y")));
        ImpliesFormula expected = new ImpliesFormula(foo, bar);
        assertThat(formula).isEqualTo(expected);
    }

    @Test
    public void fromStringIffOfPredicates() throws FormulaParsingException {
        Formula formula = parser.fromStringWithTypeChecking("Foo(x) <-> Bar(y)");
        PredicateFormula foo = new PredicateFormula("Foo", Collections.<Term>singletonList(new Constant("x")));
        PredicateFormula bar = new PredicateFormula("Bar", Collections.<Term>singletonList(new Constant("y")));
        IffFormula expected = new IffFormula(foo, bar);
        assertThat(formula).isEqualTo(expected);
    }

    @Test
    public void fromStringExplicitlyParenthesisedConnectedPredicates() throws FormulaParsingException {
        Formula formula = parser.fromStringWithTypeChecking("!(P & ((Q | R) -> (S <-> T)))");

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
        Formula formula = parser.fromStringWithTypeChecking("P -> Q & R <-> S | !T");

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
    public void fromStringShouldThrowIfUntypedTermUsedInArithmeticExpression() throws FormulaParsingException {
        parser.fromStringWithTypeChecking("Foo(x + 2)");
    }

    @Test(expected = FormulaParsingException.class)
    public void fromStringShouldThrowIfUntypedTermUsedInBooleanExpression() throws FormulaParsingException {
        parser.fromStringWithTypeChecking("x > 2");
    }

    @Test
    public void fromStringShouldTypeCheckFormula() throws FormulaParsingException, TypeMismatchException {
        SymbolTableCreator symbolTableCreator = new SymbolTableCreator();
        FormulaBuildingVisitor visitor = new FormulaBuildingVisitor(
                new TermBuildingVisitor(symbolTableCreator.create(), symbolTableCreator));

        FormulaTypeChecker mockFormulaTypeChecker = Mockito.mock(FormulaTypeChecker.class);
        parser = new ANTLRFormulaParser(visitor, mockFormulaTypeChecker);

        Formula formula = parser.fromStringWithTypeChecking("\\FORALL x in Nat. x > 2");

        verify(mockFormulaTypeChecker).analyse(formula);
    }

    @Test(expected = FormulaParsingException.class)
    public void fromStringShouldThrowIfInvalidFormulaGiven() throws FormulaParsingException {
        parser.fromStringWithTypeChecking("\\FORALL x. (Foo x & Bar(y)");
    }

}

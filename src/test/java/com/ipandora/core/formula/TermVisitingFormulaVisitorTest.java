package com.ipandora.core.formula;

import com.ipandora.api.predicate.term.Addition;
import com.ipandora.api.predicate.term.Variable;
import com.ipandora.core.term.TermVisitor;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.mockito.Mock;
import org.mockito.runners.MockitoJUnitRunner;

import static com.ipandora.testutils.FormulaCreators.*;
import static com.ipandora.testutils.TermCreators.add;
import static com.ipandora.testutils.TermCreators.natVar;
import static org.mockito.Mockito.verify;

@RunWith(MockitoJUnitRunner.class)
public class TermVisitingFormulaVisitorTest {

    private static final Variable X = natVar("x");
    private static final Variable Y = natVar("y");
    private static final Variable Z = natVar("z");
    private static final Addition ADD = add(natVar("m"), natVar("n"));

    @Mock
    private TermVisitor mockTermVisitor;

    @Test
    public void visitShouldCallTermVisitorForEachVariableInQuantifier() {
        TermVisitingFormulaVisitor visitor = new TermVisitingFormulaVisitor(mockTermVisitor);
        visitor.visit(forall(truth(), X, Y, Z));

        verify(mockTermVisitor).visit(X);
        verify(mockTermVisitor).visit(Y);
        verify(mockTermVisitor).visit(Z);
    }

    @Test
    public void visitShouldCallTermVisitorForEachParamOfPredicate() {
        TermVisitingFormulaVisitor visitor = new TermVisitingFormulaVisitor(mockTermVisitor);
        visitor.visit(pred("Foo", X, Y, ADD));

        verify(mockTermVisitor).visit(X);
        verify(mockTermVisitor).visit(Y);
        verify(mockTermVisitor).visit(ADD);
    }

    @Test
    public void visitShouldCallTermVisitorForEachSideOfEqualToFormula() {
        TermVisitingFormulaVisitor visitor = new TermVisitingFormulaVisitor(mockTermVisitor);
        visitor.visit(eq(X, ADD));

        verify(mockTermVisitor).visit(X);
        verify(mockTermVisitor).visit(ADD);
    }

    @Test
    public void visitShouldCallTermVisitorForEachSideOfGreaterThanFormula() {
        TermVisitingFormulaVisitor visitor = new TermVisitingFormulaVisitor(mockTermVisitor);
        visitor.visit(gt(X, ADD));

        verify(mockTermVisitor).visit(X);
        verify(mockTermVisitor).visit(ADD);
    }

    @Test
    public void visitShouldCallTermVisitorForEachSideOfLessThanFormula() {
        TermVisitingFormulaVisitor visitor = new TermVisitingFormulaVisitor(mockTermVisitor);
        visitor.visit(lt(X, ADD));

        verify(mockTermVisitor).visit(X);
        verify(mockTermVisitor).visit(ADD);
    }

    @Test
    public void visitShouldCallTermVisitorForEachSideOfGreaterThanEqualFormula() {
        TermVisitingFormulaVisitor visitor = new TermVisitingFormulaVisitor(mockTermVisitor);
        visitor.visit(gte(X, ADD));

        verify(mockTermVisitor).visit(X);
        verify(mockTermVisitor).visit(ADD);
    }

    @Test
    public void visitShouldCallTermVisitorForEachSideOfLessThanEqualFormula() {
        TermVisitingFormulaVisitor visitor = new TermVisitingFormulaVisitor(mockTermVisitor);
        visitor.visit(lte(X, ADD));

        verify(mockTermVisitor).visit(X);
        verify(mockTermVisitor).visit(ADD);
    }

}

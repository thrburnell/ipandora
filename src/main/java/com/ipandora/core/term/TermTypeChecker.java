package com.ipandora.core.term;

import com.ipandora.api.predicate.term.*;
import com.ipandora.api.predicate.term.Number;
import com.ipandora.core.util.WrappingRuntimeException;

public class TermTypeChecker implements TermVisitor<Void> {

    @Override
    public Void visit(Term term) {
        term.accept(this);
        return null;
    }

    @Override
    public Void visitConstant(Constant constant) {
        return null;
    }

    @Override
    public Void visitVariable(Variable variable) {
        return null;
    }

    private Void visitArithmeticExpression(ArithmeticExpression expression) {
        Term left = expression.getLeft();
        Term right = expression.getRight();

        visit(left);
        visit(right);

        if (left.getType() != Type.NAT) {
            throw new WrappingRuntimeException(new TypeMismatchException("Left term not of type Nat: " + left));
        }
        if (right.getType() != Type.NAT) {
            throw new WrappingRuntimeException(new TypeMismatchException("Right term not of type Nat: " + right));
        }

        return null;
    }

    @Override
    public Void visitAddition(Addition addition) {
        visitArithmeticExpression(addition);
        return null;
    }

    @Override
    public Void visitSubtraction(Subtraction subtraction) {
        visitArithmeticExpression(subtraction);
        return null;
    }

    @Override
    public Void visitMultiplication(Multiplication multiplication) {
        visitArithmeticExpression(multiplication);
        return null;
    }

    @Override
    public Void visitDivision(Division division) {
        visitArithmeticExpression(division);
        return null;
    }

    @Override
    public Void visitNumber(Number number) {
        return null;
    }

    @Override
    public Void visitFunction(Function function) {
        for (Term arg : function.getArgs()) {
            visit(arg);
        }
        return null;
    }

    @Override
    public Void visitPower(Power power) {
        Term base = power.getBase();
        visit(base);
        if (base.getType() != Type.NAT) {
            throw new WrappingRuntimeException(new TypeMismatchException("Base term not of type Nat: " + base));
        }
        return null;
    }

    @Override
    public Void visitSummation(Summation summation) {
        Variable variable = summation.getVariable();
        Term lowerBound = summation.getLowerBound();
        Term upperBound = summation.getUpperBound();
        Term element = summation.getElement();

        visit(lowerBound);
        visit(upperBound);
        visit(element);

        TypeMismatchException tme = null;
        if (variable.getType() != Type.NAT) {
            tme = new TypeMismatchException("Variable term not of type Nat: " + variable);
        } else if (lowerBound.getType() != Type.NAT) {
            tme = new TypeMismatchException("Lower bound term not of type Nat: " + lowerBound);
        } else if (upperBound.getType() != Type.NAT) {
            tme = new TypeMismatchException("Upper bound term not of type Nat: " + upperBound);
        } else if (element.getType() != Type.NAT) {
            tme = new TypeMismatchException("Element term not of type Nat: " + element);
        }
        if (tme != null) {
            throw new WrappingRuntimeException(tme);
        }

        return null;
    }

}
package com.ipandora.api.predicate.formula;

import com.ipandora.api.predicate.term.Term;
import com.ipandora.api.predicate.term.Type;
import com.ipandora.api.predicate.term.TypeMismatchException;

public abstract class MathematicalComparisonFormula implements Formula {

    protected final Term left;
    protected final Term right;

    public MathematicalComparisonFormula(Term left, Term right) {
        if (left.getType() != Type.NAT) {
            throw new TypeMismatchException("Left not of type Nat: " + left);
        }
        if (right.getType() != Type.NAT) {
            throw new TypeMismatchException("Right not of type Nat: " + right);
        }
        this.left = left;
        this.right = right;
    }

    public final Term getLeft() {
        return left;
    }

    public final Term getRight() {
        return right;
    }

    @Override
    public final boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        MathematicalComparisonFormula that = (MathematicalComparisonFormula) o;

        if (!left.equals(that.left)) return false;
        return right.equals(that.right);

    }

    @Override
    public final int hashCode() {
        int result = left.hashCode();
        result = 31 * result + right.hashCode();
        return result;
    }

}

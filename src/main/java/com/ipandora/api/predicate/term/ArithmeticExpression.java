package com.ipandora.api.predicate.term;

public abstract class ArithmeticExpression implements Term {

    protected final Term left;
    protected final Term right;
    protected final Type type;

    protected ArithmeticExpression(Term left, Term right) {

        if (left.getType() != Type.NAT) {
            throw new TypeMismatchException("Left term not of type Nat: " + left);
        }
        if (right.getType() != Type.NAT) {
            throw new TypeMismatchException("Right term not of type Nat: " + right);
        }

        this.left = left;
        this.right = right;
        this.type = Type.NAT;
    }

    public final Term getLeft() {
        return left;
    }

    public final Term getRight() {
        return right;
    }

    @Override
    public final Type getType() {
        return type;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        ArithmeticExpression that = (ArithmeticExpression) o;

        if (!left.equals(that.left)) return false;
        if (!right.equals(that.right)) return false;
        return type == that.type;
    }

    @Override
    public int hashCode() {
        int result = left.hashCode();
        result = 31 * result + right.hashCode();
        result = 31 * result + type.hashCode();
        return result;
    }

}

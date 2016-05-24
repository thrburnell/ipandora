package com.ipandora.core.term;

import com.ipandora.api.predicate.function.FunctionPrototype;
import com.ipandora.api.predicate.term.*;
import com.ipandora.api.predicate.term.Number;
import com.ipandora.core.util.WrappingRuntimeException;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class TermTypeChecker {

    public void analyse(Term term, List<FunctionPrototype> functionPrototypes) throws TypeMismatchException {

        Map<String, FunctionPrototype> functionPrototypeMap = new HashMap<>();
        for (FunctionPrototype prototype : functionPrototypes) {
            String name = prototype.getName();
            FunctionPrototype existingProto = functionPrototypeMap.get(name);
            if (existingProto != null && !existingProto.equals(prototype)) {
                throw new TypeMismatchException("Multiple mismatching prototypes given for function " + name);
            }

            functionPrototypeMap.put(name, prototype);
        }

        try {
            term.accept(new TermTypeCheckingVisitor(functionPrototypeMap));
        } catch (WrappingRuntimeException wre) {
            Exception wrapped = wre.getWrappedException();
            if (wrapped instanceof TypeMismatchException) {
                throw (TypeMismatchException) wrapped;
            }
            throw wre;
        }
    }

    private class TermTypeCheckingVisitor implements TermVisitor<Void> {

        // Don't need a full blown SymbolTable for this
        private final Map<String, FunctionPrototype> functionPrototypes;

        private TermTypeCheckingVisitor(Map<String, FunctionPrototype> functionPrototypes) {
            this.functionPrototypes = functionPrototypes;
        }

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

            String name = function.getName();
            FunctionPrototype prototype = functionPrototypes.get(name);
            if (prototype == null) {
                throw new WrappingRuntimeException(new TypeMismatchException("Unknown function: " + name));
            }

            Type actualType = function.getType();
            Type expectedType = prototype.getReturnType();
            if (actualType != expectedType) {
                String errorMsg = String.format("Function %s has return type %s, but expected %s",
                        name, actualType, expectedType);
                throw new WrappingRuntimeException(new TypeMismatchException(errorMsg));
            }

            List<Term> args = function.getArgs();
            List<Type> expectedArgTypes = prototype.getArgTypes();
            if (args.size() != expectedArgTypes.size()) {
                String errorMsg = String.format("Function %s has %d arguments, but expected %s",
                        name, args.size(), expectedArgTypes.size());
                throw new WrappingRuntimeException(new TypeMismatchException(errorMsg));
            }

            for (int i = 0; i < args.size(); i++) {
                Type actual = args.get(i).getType();
                Type expected = expectedArgTypes.get(i);
                if (actual != expected) {
                    String errorMsg = String.format("Function %s has type %s for argument %d, but expected %s",
                            name, actual, i, expected);
                    throw new WrappingRuntimeException(new TypeMismatchException(errorMsg));
                }
                visit(args.get(i));
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
    }

}

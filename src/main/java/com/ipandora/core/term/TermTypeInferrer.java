package com.ipandora.core.term;

import com.ipandora.api.predicate.function.FunctionPrototype;
import com.ipandora.api.predicate.term.*;
import com.ipandora.api.predicate.term.Number;
import com.ipandora.core.util.WrappingRuntimeException;

import java.util.*;

public class TermTypeInferrer {

    public void infer(Term term) throws TypeMismatchException {
        try {
            TermTypeInferringVisitor visitor = new TermTypeInferringVisitor();

            // Visitor returns true if something changed. Terminate inference as soon as changes are no longer made.
            while (visitor.visit(term));

        } catch (WrappingRuntimeException wre) {
            Exception wrappedException = wre.getWrappedException();

            if (wrappedException instanceof TypeMismatchException) {
                throw (TypeMismatchException) wrappedException;
            }

            throw wre;
        }
    }

    private class TermTypeInferringVisitor implements TermVisitor<Boolean> {

        private Stack<Type> typeStack = new Stack<>();
        private SymbolTable symbolTable = new SymbolTableImpl();
        private Map<String, FunctionPrototype> functionPrototypesByName = new HashMap<>();

        @Override
        public Boolean visit(Term term) {
            return term.accept(this);
        }

        @Override
        public Boolean visitConstant(Constant constant) {

            String name = constant.getName();

            if (inferTypeFromStack(constant)) {
                // Add new type to symbol table
                symbolTable.addMapping(name, constant.getType());
                return true;
            }

            return inferTypeFromSymbolTable(constant, name);
        }

        @Override
        public Boolean visitVariable(Variable variable) {

            String name = variable.getName();

            if (inferTypeFromStack(variable)) {
                // Add new type to symbol table
                symbolTable.addMapping(name, variable.getType());
                return true;
            }

            return inferTypeFromSymbolTable(variable, name);
        }

        @Override
        public Boolean visitAddition(Addition addition) {
            return visitArithmeticExpression(addition);
        }

        @Override
        public Boolean visitSubtraction(Subtraction subtraction) {
            return visitArithmeticExpression(subtraction);
        }

        @Override
        public Boolean visitMultiplication(Multiplication multiplication) {
            return visitArithmeticExpression(multiplication);
        }

        @Override
        public Boolean visitDivision(Division division) {
            return visitArithmeticExpression(division);
        }

        @Override
        public Boolean visitNumber(Number number) {
            if (!typeStack.isEmpty() && typeStack.peek() != Type.NAT) {
                String errorMsg = String.format("Trying to infer type %s on Number.", typeStack);
                throw new WrappingRuntimeException(new TypeMismatchException(errorMsg));
            }

            return false;
        }

        @Override
        public Boolean visitFunction(Function function) {

            String name = function.getName();
            FunctionPrototype oldProto = functionPrototypesByName.get(name);
            boolean changedProto;

            // Infer return type
            changedProto = inferTypeFromStack(function);

            // Infer arg types
            List<Type> newArgTypes = new ArrayList<>();
            for (Term arg : function.getArgs()) {
                Stack<Type> oldTypeStack = typeStack;
                typeStack = new Stack<>();
                changedProto |= visit(arg);
                typeStack = oldTypeStack;
                newArgTypes.add(arg.getType());
            }

            if (oldProto != null) {
                Type oldReturnType = oldProto.getReturnType();
                if (oldReturnType != Type.UNKNOWN) {
                    changedProto |= attemptToSetType(function, oldReturnType);
                }

                List<Term> args = function.getArgs();
                List<Type> argTypes = oldProto.getArgTypes();
                for (int i = 0; i < argTypes.size(); i++) {
                    Type argType = argTypes.get(i);
                    if (argType != Type.UNKNOWN) {
                        Term arg = args.get(i);
                        typeStack.push(argType);
                        boolean changedArg = visit(arg);
                        typeStack.pop();

                        changedProto |= changedArg;

                        if (changedArg) {
                            newArgTypes.remove(i);
                            newArgTypes.add(i, arg.getType());
                        }
                    }
                }
            }

            if (changedProto) {
                FunctionPrototype newProto = new FunctionPrototype(name, newArgTypes, function.getType());
                functionPrototypesByName.put(name, newProto);
            }

            return changedProto;
        }

        @Override
        public Boolean visitPower(Power power) {
            typeStack.push(Type.NAT);
            boolean changed = visit(power.getBase());
            typeStack.pop();
            return changed;
        }

        private boolean inferTypeFromStack(Atom atom) {
            return !typeStack.isEmpty() && attemptToSetType(atom, typeStack.peek());

        }

        private boolean inferTypeFromSymbolTable(Atom atom, String name) {
            Type type = symbolTable.getType(name);
            return type != null && attemptToSetType(atom, type);
        }

        private boolean attemptToSetType(Atom atom, Type type) {

            if (atom.getType() == type) {
                return false;
            }

            if (atom.getType() != Type.UNKNOWN) {
                // Type is already known and conflicts with what is being inferred
                String errorMsg = String.format("Need to infer type %s for %s, but already typed as %s.",
                        type, atom, atom.getType());
                throw new WrappingRuntimeException(new TypeMismatchException(errorMsg));
            }

            atom.setType(type);
            return true;
        }

        private Boolean visitArithmeticExpression(ArithmeticExpression arithmeticExpression) {
            typeStack.push(Type.NAT);
            boolean changedLeft = visit(arithmeticExpression.getLeft());
            boolean changedRight = visit(arithmeticExpression.getRight());
            typeStack.pop();

            return changedLeft || changedRight;
        }

    }

}

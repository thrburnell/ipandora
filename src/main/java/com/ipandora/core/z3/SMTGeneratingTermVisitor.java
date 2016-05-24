package com.ipandora.core.z3;

import com.ipandora.api.predicate.function.FunctionPrototype;
import com.ipandora.api.predicate.term.*;
import com.ipandora.api.predicate.term.Number;
import com.ipandora.core.term.TermVisitor;
import com.ipandora.core.util.CollectionUtils;
import com.ipandora.core.util.WrappingRuntimeException;
import org.apache.commons.lang3.StringUtils;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class SMTGeneratingTermVisitor implements TermVisitor<String> {

    private final Map<String, Type> constantNamesToTypes = new HashMap<>();
    private final Map<String, FunctionPrototype> functionPrototypesByName = new HashMap<>();

    public Map<String, Type> getConstantNamesToTypes() {
        return constantNamesToTypes;
    }

    public List<FunctionPrototype> getFunctionPrototypes() {
        return CollectionUtils.extractMapValues(functionPrototypesByName);
    }

    @Override
    public String visit(Term term) {
        return term.accept(this);
    }

    @Override
    public String visitConstant(Constant constant) {
        saveConstant(constant);
        return constant.getName();
    }

    @Override
    public String visitVariable(Variable variable) {
        return variable.getName();
    }

    @Override
    public String visitAddition(Addition addition) {
        String left = visit(addition.getLeft());
        String right = visit(addition.getRight());
        return String.format("(+ %s %s)", left, right);
    }

    @Override
    public String visitSubtraction(Subtraction subtraction) {
        String left = visit(subtraction.getLeft());
        String right = visit(subtraction.getRight());
        return String.format("(- %s %s)", left, right);
    }

    @Override
    public String visitMultiplication(Multiplication multiplication) {
        String left = visit(multiplication.getLeft());
        String right = visit(multiplication.getRight());
        return String.format("(* %s %s)", left, right);
    }

    @Override
    public String visitDivision(Division division) {
        String left = visit(division.getLeft());
        String right = visit(division.getRight());
        return String.format("(/ %s %s)", left, right);
    }

    @Override
    public String visitNumber(Number number) {
        return String.valueOf(number.getNumber());
    }

    @Override
    public String visitFunction(Function function) {
        saveFunction(function);

        List<String> argStrings = new ArrayList<>();
        for (Term arg : function.getArgs()) {
            argStrings.add(visit(arg));
        }

        String argString = StringUtils.join(argStrings, " ");
        return String.format("(%s %s)", function.getName(), argString);
    }

    @Override
    public String visitPower(Power power) {
        Term base = power.getBase();
        int exponent = power.getExponent();
        String baseString = visit(base);

        return String.format("(^ %s %d)", baseString, exponent);
    }

    private void saveConstant(Constant constant) {
        String name = constant.getName();
        Type type = constant.getType();

        Type existingType = constantNamesToTypes.get(name);

        if (existingType != null && !existingType.equals(type)) {
            String errorMsg = String.format("Constant %s used in conflicting type contexts: " +
                    "One use: %s; Another use: %s.", name, existingType, type);
            throw new WrappingRuntimeException(new TypeMismatchException(errorMsg));
        } else if (existingType == null) {
            constantNamesToTypes.put(name, type);
        }
    }

    private void saveFunction(Function function) {
        String name = function.getName();

        FunctionPrototype newPrototype = FunctionPrototype.fromFunctionTerm(function);
        FunctionPrototype existingPrototype = functionPrototypesByName.get(name);

        if (existingPrototype != null && !existingPrototype.equals(newPrototype)) {

            String errorMsg = String.format("Function %s called multiple times with different argument types: " +
                    "One invocation: %s; Another invocation: %s.", name, existingPrototype.getArgTypes(),
                    newPrototype.getArgTypes());
            throw new WrappingRuntimeException(new TypeMismatchException(errorMsg));

        } else if (existingPrototype == null) {
            functionPrototypesByName.put(name, newPrototype);
        }
    }

}

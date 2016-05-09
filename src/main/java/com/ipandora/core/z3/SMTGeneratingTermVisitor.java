package com.ipandora.core.z3;

import com.ipandora.api.predicate.term.*;
import com.ipandora.api.predicate.term.Number;
import com.ipandora.core.term.TermVisitor;
import org.apache.commons.lang3.StringUtils;

import java.util.*;

public class SMTGeneratingTermVisitor implements TermVisitor<String> {

    private final Set<String> constants = new HashSet<>();
    private final Map<String, Integer> functions = new HashMap<>();

    public Set<String> getConstants() {
        return constants;
    }

    public Map<String, Integer> getFunctions() {
        return functions;
    }

    @Override
    public String visit(Term term) {
        return term.accept(this);
    }

    @Override
    public String visitConstant(Constant constant) {
        String name = constant.getName();
        constants.add(name);
        return name;
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
        String name = function.getName();
        List<Term> args = function.getArgs();
        functions.put(name, args.size());

        List<String> argStrings = new ArrayList<>();
        for (Term arg : args) {
            argStrings.add(visit(arg));
        }

        String argString = StringUtils.join(argStrings, " ");

        return String.format("(%s %s)", name, argString);
    }

}

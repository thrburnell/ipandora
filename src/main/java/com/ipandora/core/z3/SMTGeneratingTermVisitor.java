package com.ipandora.core.z3;

import com.ipandora.api.predicate.term.Constant;
import com.ipandora.api.predicate.term.Term;
import com.ipandora.api.predicate.term.Variable;
import com.ipandora.core.term.TermVisitor;

import java.util.HashSet;
import java.util.Set;

public class SMTGeneratingTermVisitor implements TermVisitor<String> {

    private final Set<String> constants = new HashSet<>();

    public Set<String> getConstants() {
        return constants;
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

}

package com.ipandora.core.term;

import com.ipandora.api.predicate.term.Constant;
import com.ipandora.api.predicate.term.Term;
import com.ipandora.api.predicate.term.Variable;

public interface TermVisitor<T> {

    T visit(Term term);
    T visitConstant(Constant constant);
    T visitVariable(Variable variable);

}

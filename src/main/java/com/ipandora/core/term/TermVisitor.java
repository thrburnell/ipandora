package com.ipandora.core.term;

import com.ipandora.api.predicate.term.*;
import com.ipandora.api.predicate.term.Number;

public interface TermVisitor<T> {

    T visit(Term term);
    T visitConstant(Constant constant);
    T visitVariable(Variable variable);
    T visitAddition(Addition addition);
    T visitSubtraction(Subtraction subtraction);
    T visitMultiplication(Multiplication multiplication);
    T visitDivision(Division division);
    T visitNumber(Number number);
    T visitFunction(Function function);
    T visitPower(Power power);
    T visitSummation(Summation summar);

}

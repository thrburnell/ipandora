package com.ipandora.testutils;

import com.ipandora.api.predicate.term.*;
import com.ipandora.api.predicate.term.Number;

import java.util.Arrays;

public class TermCreators {
    
    public static Variable natVar(String name) {
        return Variable.withTypeNat(name);
    }
    
    public static Variable var(String name) {
        return new Variable(name);
    }

    public static Constant natCon(String name) {
        return new Constant(name, Type.NAT);
    }

    public static Constant con(String name) {
        return new Constant(name);
    }
    
    public static Function fun(String name, Term... args) {
        return new Function(name, Arrays.asList(args));
    }

    public static Function natFun(String name, Term... args) {
        return new Function(name, Arrays.asList(args), Type.NAT);
    }

    public static Number num(int n) {
        return new Number(n);
    }
    
    public static Addition add(Term t1, Term t2, Term... ts) {
        Addition addition = new Addition(t1, t2);
        
        for (Term t : ts) {
            addition = new Addition(addition, t);
        }
        
        return addition;
    }
    
    public static Subtraction sub(Term t1, Term t2, Term... ts) {
        Subtraction subtraction = new Subtraction(t1, t2);

        for (Term t : ts) {
            subtraction = new Subtraction(subtraction, t);
        }

        return subtraction;
    }

    public static Multiplication mul(Term t1, Term t2, Term... ts) {
        Multiplication multiplication = new Multiplication(t1, t2);

        for (Term t : ts) {
            multiplication = new Multiplication(multiplication, t);
        }

        return multiplication;
    }

    public static Division div(Term t1, Term t2, Term... ts) {
        Division division = new Division(t1, t2);

        for (Term t : ts) {
            division = new Division(division, t);
        }

        return division;
    }

    public static Power pow(Term t, int n) {
        return new Power(t, n);
    }
    
}

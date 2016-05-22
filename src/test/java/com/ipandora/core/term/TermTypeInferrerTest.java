package com.ipandora.core.term;

import com.ipandora.api.predicate.term.*;
import org.junit.Test;

import static com.ipandora.testutils.TermCreators.*;
import static org.assertj.core.api.Assertions.assertThat;

public class TermTypeInferrerTest {

    @Test
    public void inferConstantShouldLeaveTypeUnknown() throws TypeMismatchException {
        // c
        Constant c = con("c");
        TermTypeInferrer inferrer = new TermTypeInferrer();
        inferrer.infer(c);

        assertThat(c.getType()).isEqualTo(Type.UNKNOWN);
    }

    @Test
    public void inferConstantShouldLeaveTypeNat() throws TypeMismatchException {
        // c
        Constant c = natCon("c");
        TermTypeInferrer inferrer = new TermTypeInferrer();
        inferrer.infer(c);

        assertThat(c.getType()).isEqualTo(Type.NAT);
    }

    @Test
    public void inferVariableShouldLeaveTypeUnknown() throws TypeMismatchException {
        // x
        Variable x = var("x");
        TermTypeInferrer inferrer = new TermTypeInferrer();
        inferrer.infer(x);

        assertThat(x.getType()).isEqualTo(Type.UNKNOWN);
    }

    @Test
    public void inferVariableShouldLeaveTypeNat() throws TypeMismatchException {
        // x
        Variable x = natVar("x");
        TermTypeInferrer inferrer = new TermTypeInferrer();
        inferrer.infer(x);

        assertThat(x.getType()).isEqualTo(Type.NAT);
    }

    @Test
    public void inferFunctionShouldLeaveTypeUnknown() throws TypeMismatchException {
        // f(x)
        Function fun = fun("f", var("x"));
        TermTypeInferrer inferrer = new TermTypeInferrer();
        inferrer.infer(fun);

        assertThat(fun.getType()).isEqualTo(Type.UNKNOWN);
    }

    @Test
    public void inferFunctionShouldLeaveTypeNat() throws TypeMismatchException {
        // f(x)
        Function fun = natFun("f", var("x"));
        TermTypeInferrer inferrer = new TermTypeInferrer();
        inferrer.infer(fun);

        assertThat(fun.getType()).isEqualTo(Type.NAT);
    }

    @Test
    public void inferAdditionShouldInferNatTypeForAllSubTerms() throws TypeMismatchException {
        // c + x + f(y)
        Constant c = con("c");
        Variable x = var("x");
        Variable y = var("y");
        Function fun = fun("f", y);
        Addition add = add(c, x, fun);
        TermTypeInferrer inferrer = new TermTypeInferrer();
        inferrer.infer(add);

        assertThat(c.getType()).isEqualTo(Type.NAT);
        assertThat(x.getType()).isEqualTo(Type.NAT);
        assertThat(fun.getType()).isEqualTo(Type.NAT);
    }

    @Test
    public void inferFunctionShouldNotInferTypesForParametersIfNotKnown() throws TypeMismatchException {
        // f(x) + y
        Variable x = var("x");
        Function fun = fun("f", x);
        Variable y = var("y");
        TermTypeInferrer inferrer = new TermTypeInferrer();
        inferrer.infer(add(fun, y));

        assertThat(x.getType()).isEqualTo(Type.UNKNOWN);
    }

    @Test
    public void inferShouldInferTypeOfFunctionParameterFromKnownTypeOfParameterInOtherInvocation()
            throws TypeMismatchException {
        // f(x) + f(c) + x     => c should have same type as x!
        Variable x1 = var("x");
        Variable x2 = var("x");
        Constant c = con("c");
        Function f1 = fun("f", x1);
        Function f2 = fun("f", c);
        Addition add = add(f1, f2, x2);
        TermTypeInferrer inferrer = new TermTypeInferrer();
        inferrer.infer(add);

        assertThat(c.getType()).isEqualTo(x1.getType()).isEqualTo(x2.getType()).isEqualTo(Type.NAT);
    }

    @Test
    public void inferShouldInferTypesOfAllFunctionParametersFromKnownTypesOfParametersInOtherInvocation()
            throws TypeMismatchException {
        // x + g(x, x) + g(x, y)
        Variable x1 = var("x");
        Variable x2 = var("x");
        Variable x3 = var("x");
        Variable x4 = var("x");
        Variable y = var("y");
        Function g1 = fun("g", x1, x2);
        Function g2 = fun("g", x3, y);
        Addition add = add(x4, g1, g2);
        TermTypeInferrer inferrer = new TermTypeInferrer();
        inferrer.infer(add);

        assertThat(y.getType()).isEqualTo(x1.getType()).isEqualTo(x2.getType()).isEqualTo(x3.getType())
                .isEqualTo(x4.getType()).isEqualTo(Type.NAT);
    }

    @Test
    public void inferShouldInferTypeOfFunctionParameters() throws TypeMismatchException {
        // x + f(x)
        Variable x1 = var("x");
        Variable x2 = var("x");
        Function f = fun("f", x2);
        Addition add = add(x1, f);
        TermTypeInferrer inferrer = new TermTypeInferrer();
        inferrer.infer(add);

        assertThat(x2.getType()).isEqualTo(Type.NAT);
    }

    @Test
    public void inferShouldInferFunctionReturnTypeWhenUsedInPower() throws TypeMismatchException {
        // f(x) ^ 3
        Function fun = fun("f", var("x"));
        Power pow = pow(fun, 3);
        TermTypeInferrer inferrer = new TermTypeInferrer();
        inferrer.infer(pow);

        assertThat(fun.getType()).isEqualTo(Type.NAT);
    }

    @Test
    public void inferComplexCase1() throws TypeMismatchException {
        // x + f(x) + f(c) + g(c) + g(d)  => d should have the same type as x!

        Variable x1 = var("x");
        Variable x2 = var("x");
        Constant c1 = con("c");
        Constant c2 = con("c");
        Constant d = con("d");
        Function f1 = fun("f", x2);
        Function f2 = fun("f", c1);
        Function g1 = fun("g", c2);
        Function g2 = fun("g", d);
        Addition add = add(x1, f1, f2, g1, g2);
        TermTypeInferrer inferrer = new TermTypeInferrer();
        inferrer.infer(add);

        assertThat(d.getType()).isEqualTo(Type.NAT);
    }

    @Test
    public void inferComplexCase2() throws TypeMismatchException {
        // f(x + 2) + g(x) + g(c)  => c should have the same type as x, Nat!

        Variable x1 = var("x");
        Variable x2 = var("x");
        Constant c = con("c");
        Function f = fun("f", add(x1, num(2)));
        Function g1 = fun("g", x2);
        Function g2 = fun("g", c);
        Addition add = add(f, g1, g2);
        TermTypeInferrer inferrer = new TermTypeInferrer();
        inferrer.infer(add);

        assertThat(c.getType()).isEqualTo(Type.NAT);
    }

    @Test
    public void inferComplexCase3() throws TypeMismatchException {
        // f(g(x)) + g(2) + f(y) + y  => x type Nat, g(x) type same as y (Nat)

        Variable x = var("x");
        Variable y1 = var("y");
        Variable y2 = var("y");
        Function g1 = fun("g", x);
        Function f1 = fun("f", g1);
        Function g2 = fun("g", num(2));
        Function f2 = fun("f", y1);
        Addition add = add(f1, g2, f2, y2);

        TermTypeInferrer inferrer = new TermTypeInferrer();
        inferrer.infer(add);

        assertThat(x.getType()).isEqualTo(Type.NAT);
        assertThat(g1.getType()).isEqualTo(y1.getType()).isEqualTo(Type.NAT);
    }

    @Test
    public void inferFoo() throws TypeMismatchException {
        // f(g(x)) + x

        Variable x1 = var("x");
        Function g = fun("g", x1);
        Function f = fun("f", g);
        Variable x2 = var("x");
        Addition add = add(f, x2);
        TermTypeInferrer inferrer = new TermTypeInferrer();
        inferrer.infer(add);

        assertThat(x1.getType()).isEqualTo(Type.NAT);
    }

}

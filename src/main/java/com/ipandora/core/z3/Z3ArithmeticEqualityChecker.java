package com.ipandora.core.z3;

import com.ipandora.api.predicate.formula.EqualToFormula;
import com.ipandora.api.predicate.formula.ForallFormula;
import com.ipandora.api.predicate.formula.Formula;
import com.ipandora.api.predicate.formula.NotFormula;
import com.ipandora.api.predicate.term.Term;
import com.ipandora.api.predicate.term.Variable;
import com.ipandora.core.formula.TermVisitingFormulaVisitor;
import com.ipandora.core.proof.ArithmeticEqualityChecker;
import com.ipandora.core.proof.ProofStepCheckException;
import com.ipandora.core.term.AtomCollectingTermVisitor;
import com.ipandora.core.util.ProcessTimeoutException;

import java.io.IOException;
import java.util.Set;

public class Z3ArithmeticEqualityChecker implements ArithmeticEqualityChecker {

    private final SMTCodeGenerator smtCodeGenerator;
    private final Z3Client z3Client;

    public Z3ArithmeticEqualityChecker(SMTCodeGenerator smtCodeGenerator, Z3Client z3Client) {
        this.smtCodeGenerator = smtCodeGenerator;
        this.z3Client = z3Client;
    }

    @Override
    public boolean check(Term t1, Term t2) throws ProofStepCheckException {

        Formula formula = new EqualToFormula(t1, t2);

        AtomCollectingTermVisitor termVisitor = new AtomCollectingTermVisitor();
        TermVisitingFormulaVisitor formulaVisitor = new TermVisitingFormulaVisitor(termVisitor);
        formulaVisitor.visit(formula);

        Set<Variable> freeVariables = termVisitor.getUniqueVariables();

        if (!freeVariables.isEmpty()) {
            formula = new ForallFormula(formula, freeVariables.toArray(new Variable[freeVariables.size()]));
        }

        NotFormula notFormula = new NotFormula(formula);

        String program;
        try {
            program = smtCodeGenerator.generateCheckSatCode(notFormula);
        } catch (Z3InvalidProblemException e) {
            throw new ProofStepCheckException(e.getMessage());
        }

        try {
            return !z3Client.isSat(program);
        } catch (ProcessTimeoutException e) {
            throw new ProofStepCheckException("Unable to determine validity of proof step before timeout. " +
                    "Try providing more assertions.");
        } catch (IOException | Z3UnrecognisableOutputException e) {
            throw new ProofStepCheckException(e);
        } catch (Z3UnknownException e) {
            throw new ProofStepCheckException("Unable to determine validity of proof step");
        }
    }

}

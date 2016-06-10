package com.ipandora.core.z3;

import com.ipandora.api.predicate.formula.Formula;
import com.ipandora.api.predicate.formula.NotFormula;
import com.ipandora.api.predicate.formula.OrFormula;
import com.ipandora.core.proof.ExhaustiveCaseChecker;
import com.ipandora.core.proof.ProofStepCheckException;
import com.ipandora.core.util.ProcessTimeoutException;

import java.io.IOException;

public class Z3ExhaustiveCaseChecker implements ExhaustiveCaseChecker {

    private final SMTCodeGenerator codeGenerator;
    private final Z3Client z3Client;

    public Z3ExhaustiveCaseChecker(SMTCodeGenerator codeGenerator, Z3Client z3Client) {
        this.codeGenerator = codeGenerator;
        this.z3Client = z3Client;
    }

    @Override
    public boolean check(Formula f1, Formula f2) throws ProofStepCheckException {

        // The two formulas are exhaustive if (f1 OR f2) is valid, i.e.
        // if ~(f1 OR f2) is unsatisfiable.
        OrFormula orFormula = new OrFormula(f1, f2);
        NotFormula notFormula = new NotFormula(orFormula);

        String program;
        try {
            program = codeGenerator.generateCheckSatCode(notFormula);
        } catch (Z3InvalidProblemException e) {
            throw new ProofStepCheckException(e.getMessage());
        }

        try {
            return !z3Client.isSat(program);
        } catch (IOException | Z3UnrecognisableOutputException | ProcessTimeoutException e) {
            e.printStackTrace();
            throw new ProofStepCheckException(e);
        } catch (Z3UnknownException e) {
            throw new ProofStepCheckException("Unable to determine validity of proof step");
        }
    }

}

package com.ipandora.core.z3;

import com.ipandora.api.predicate.formula.Formula;
import com.ipandora.api.predicate.formula.ImpliesFormula;
import com.ipandora.api.predicate.formula.NotFormula;
import com.ipandora.core.formula.FormulaReducer;
import com.ipandora.core.proof.ImpliesChecker;
import com.ipandora.core.proof.ProofStepCheckException;
import com.ipandora.core.util.ProcessTimeoutException;

import java.io.IOException;
import java.util.List;

public class Z3ImpliesChecker implements ImpliesChecker {

    private final SMTCodeGenerator codeGenerator;
    private final Z3Client z3Client;
    private final FormulaReducer conjunctor;

    public Z3ImpliesChecker(SMTCodeGenerator codeGenerator, Z3Client z3Client,
                            FormulaReducer conjunctor) {
        this.codeGenerator = codeGenerator;
        this.z3Client = z3Client;
        this.conjunctor = conjunctor;
    }

    @Override
    public boolean check(List<Formula> assumptions, Formula goal) throws ProofStepCheckException {

        if (assumptions.isEmpty()) {
            // Could check whether goal is equivalent to true
            throw new ProofStepCheckException("No assumptions given");
        }

        Formula assumption = conjunctor.reduce(assumptions);
        ImpliesFormula impliesFormula = new ImpliesFormula(assumption, goal);

        // Recall F is valid <=> !F is not satisfiable
        NotFormula notFormula = new NotFormula(impliesFormula);

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

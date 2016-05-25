package com.ipandora.core.z3;

import com.ipandora.api.predicate.formula.AndFormula;
import com.ipandora.api.predicate.formula.EqualToFormula;
import com.ipandora.api.predicate.formula.ForallFormula;
import com.ipandora.api.predicate.formula.NotFormula;
import com.ipandora.api.predicate.function.FunctionDefinition;
import com.ipandora.api.predicate.term.Term;
import com.ipandora.core.function.FunctionDefinitionEncoder;
import com.ipandora.core.proof.FunctionEqualityChecker;
import com.ipandora.core.proof.ProofStepCheckException;
import com.ipandora.core.util.ProcessTimeoutException;

import java.io.IOException;

public class Z3FunctionEqualityChecker implements FunctionEqualityChecker {

    private final SMTCodeGenerator smtCodeGenerator;
    private final Z3Client z3Client;
    private final FunctionDefinitionEncoder encoder;

    public Z3FunctionEqualityChecker(SMTCodeGenerator smtCodeGenerator, Z3Client z3Client,
                                     FunctionDefinitionEncoder encoder) {
        this.smtCodeGenerator = smtCodeGenerator;
        this.z3Client = z3Client;
        this.encoder = encoder;
    }

    @Override
    public boolean check(Term t1, Term t2, FunctionDefinition functionDefinition) throws ProofStepCheckException {

        // In order for t1 and t2 to be equal given the function definition, we want to check whether
        // encode(functionDefinition) & !(t1 = t2)  is sat (if unsat then equality is true)
        EqualToFormula equalToFormula = new EqualToFormula(t1, t2);
        NotFormula notFormula = new NotFormula(equalToFormula);

        // TODO: ensure terms t1 and t2 contain no terms with names that clash with functionEncoded!
        ForallFormula functionEncoded = encoder.encode(functionDefinition);
        AndFormula andFormula = new AndFormula(functionEncoded.getFormula(), notFormula);
        ForallFormula forallFormula = new ForallFormula(functionEncoded.getVariablesByType(), andFormula);

        String program;
        try {
            program = smtCodeGenerator.generateCheckSatCode(forallFormula);
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

package com.ipandora.resources;

import com.ipandora.api.predicate.formula.Formula;
import com.ipandora.api.predicate.proofstep.StepRequest;
import com.ipandora.api.predicate.proofstep.StepResponse;
import com.ipandora.api.predicate.validate.ValidateRequest;
import com.ipandora.api.predicate.validate.ValidateResponse;
import com.ipandora.core.formula.FormulaParser;
import com.ipandora.core.formula.ImpliesChecker;
import com.ipandora.core.formula.ImpliesCheckerException;

import javax.ws.rs.Consumes;
import javax.ws.rs.POST;
import javax.ws.rs.Path;
import javax.ws.rs.Produces;
import javax.ws.rs.core.MediaType;
import java.util.ArrayList;
import java.util.List;

@Path("/predicate")
@Produces(MediaType.APPLICATION_JSON)
@Consumes(MediaType.APPLICATION_JSON)
public class PredicateResource {

    private final FormulaParser formulaParser;
    private final ImpliesChecker impliesChecker;

    public PredicateResource(FormulaParser formulaParser, ImpliesChecker impliesChecker) {
        this.formulaParser = formulaParser;
        this.impliesChecker = impliesChecker;
    }


    @POST
    @Path("/formula")
    public ValidateResponse validateFormula(ValidateRequest validateRequest) {

        ValidateResponse validateResponse = new ValidateResponse();
        validateResponse.setFormula(validateRequest.getFormula());
        validateResponse.setSyntaxValid(false);
        validateResponse.setErrorMsg("Validation not yet implemented");
        return validateResponse;
    }

    @POST
    @Path("/step")
    public StepResponse checkProofStep(StepRequest stepRequest) throws ImpliesCheckerException {

        List<String> assumptions = stepRequest.getAssumptions();

        List<Formula> assumptionFormulas = new ArrayList<>();
        for (String assumption : assumptions) {
            assumptionFormulas.add(formulaParser.fromString(assumption));
        }

        Formula goalFormula = formulaParser.fromString(stepRequest.getGoal());

        boolean result = impliesChecker.check(assumptionFormulas, goalFormula);

        StepResponse stepResponse = new StepResponse();
        stepResponse.setAssumptions(stepRequest.getAssumptions());
        stepResponse.setGoal(stepRequest.getGoal());
        stepResponse.setValidityPreserved(result);

        if (!result) {
            stepResponse.setErrorMsg("Error messages not yet implemented.");
        }

        return stepResponse;
    }

}

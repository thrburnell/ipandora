package com.ipandora.resources;

import com.ipandora.api.predicate.proofstep.StepRequest;
import com.ipandora.api.predicate.proofstep.StepResponse;
import com.ipandora.api.predicate.validate.ValidateRequest;
import com.ipandora.api.predicate.validate.ValidateResponse;

import javax.ws.rs.Consumes;
import javax.ws.rs.POST;
import javax.ws.rs.Path;
import javax.ws.rs.Produces;
import javax.ws.rs.core.MediaType;

@Path("/predicate")
@Produces(MediaType.APPLICATION_JSON)
@Consumes(MediaType.APPLICATION_JSON)
public class PredicateResource {

    @POST
    @Path("/formula")
    public ValidateResponse validateFormula(ValidateRequest validateRequest) {

        ValidateResponse validateResponse = new ValidateResponse();
        validateResponse.setFormula(validateRequest.getFormula());
        validateResponse.setSyntaxValid(false);
        validateResponse.setErrorMsg("Validation not yet implemented");
        return validateResponse;

//        String formula = validateRequest.getFormula();
//        ANTLRInputStream stream = new ANTLRInputStream(formula);
//        PredicateLogicLexer lexer = new PredicateLogicLexer(stream);
//        CommonTokenStream tokens = new CommonTokenStream(lexer);
//        PredicateLogicParser parser = new PredicateLogicParser(tokens);
//        PredicateLogicParser.FormulaContext formulaCtx = parser.formula();
//        FormulaBuildingVisitor visitor = new FormulaBuildingVisitor();
//        return new ValidateRequest(visitor.visit(formulaCtx).toString());
    }

    @POST
    @Path("/step")
    public StepResponse checkProofStep(StepRequest stepRequest) {

        StepResponse stepResponse = new StepResponse();
        stepResponse.setAssumptions(stepRequest.getAssumptions());
        stepResponse.setGoal(stepRequest.getGoal());
        stepResponse.setValidityPreserved(false);
        stepResponse.setErrorMsg("Proof step checking not yet implemented");
        return stepResponse;
    }

}

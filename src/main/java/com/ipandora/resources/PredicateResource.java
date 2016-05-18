package com.ipandora.resources;

import com.ipandora.api.predicate.formula.ForallFormula;
import com.ipandora.api.predicate.formula.Formula;
import com.ipandora.api.predicate.induction.SchemaRequest;
import com.ipandora.api.predicate.induction.SchemaResponse;
import com.ipandora.api.predicate.proofstep.StepRequest;
import com.ipandora.api.predicate.proofstep.StepResponse;
import com.ipandora.api.predicate.read.ReadResponse;
import com.ipandora.api.predicate.term.Term;
import com.ipandora.api.predicate.validate.ValidateRequest;
import com.ipandora.api.predicate.validate.ValidateResponse;
import com.ipandora.core.formula.FormulaParser;
import com.ipandora.core.formula.FormulaParsingException;
import com.ipandora.core.induction.InductionSchema;
import com.ipandora.core.induction.InductionSchemaGenerator;
import com.ipandora.core.induction.SchemaGeneratorException;
import com.ipandora.core.proof.*;
import com.ipandora.core.util.PrettyStringBuilder;
import org.glassfish.jersey.media.multipart.FormDataContentDisposition;
import org.glassfish.jersey.media.multipart.FormDataParam;

import javax.ws.rs.Consumes;
import javax.ws.rs.POST;
import javax.ws.rs.Path;
import javax.ws.rs.Produces;
import javax.ws.rs.core.MediaType;
import javax.ws.rs.core.Response;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

@Path("/predicate")
@Produces(MediaType.APPLICATION_JSON)
@Consumes(MediaType.APPLICATION_JSON)
public class PredicateResource {

    private final FormulaParser formulaParser;
    private final ImpliesChecker impliesChecker;
    private final ProofStreamReaderCreator proofStreamReaderCreator;
    private final InductionSchemaGenerator inductionSchemaGenerator;
    private final PrettyStringBuilder<Formula> formulaStringBuilder;
    private final PrettyStringBuilder<Term> termStringBuilder;

    public PredicateResource(FormulaParser formulaParser, ImpliesChecker impliesChecker,
                             ProofStreamReaderCreator proofStreamReaderCreator,
                             InductionSchemaGenerator inductionSchemaGenerator,
                             PrettyStringBuilder<Formula> formulaStringBuilder,
                             PrettyStringBuilder<Term> termStringBuilder) {
        this.formulaParser = formulaParser;
        this.impliesChecker = impliesChecker;
        this.proofStreamReaderCreator = proofStreamReaderCreator;
        this.inductionSchemaGenerator = inductionSchemaGenerator;
        this.formulaStringBuilder = formulaStringBuilder;
        this.termStringBuilder = termStringBuilder;
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
    public StepResponse checkProofStep(StepRequest stepRequest)
            throws ImpliesCheckerException, FormulaParsingException {

        String method = stepRequest.getMethod();

        if (method.equals(ProofStepMethods.LOGICAL_IMPLICATION)) {

            List<String> assumptions = stepRequest.getAssumptions();

            List<Formula> assumptionFormulas = new ArrayList<>();
            for (String assumption : assumptions) {
                assumptionFormulas.add(formulaParser.fromString(assumption));
            }

            Formula goalFormula = formulaParser.fromString(stepRequest.getGoal());

            boolean result = impliesChecker.check(assumptionFormulas, goalFormula);

            StepResponse stepResponse = new StepResponse();
            stepResponse.setMethod(method);
            stepResponse.setGoal(stepRequest.getGoal());
            stepResponse.setAssumptions(stepRequest.getAssumptions());
            stepResponse.setValid(result);

            if (!result) {
                stepResponse.setErrorMsg("Error messages not yet implemented.");
            }

            return stepResponse;
        }

        StepResponse unknownMethodResponse = new StepResponse();
        unknownMethodResponse.setMethod(method);
        unknownMethodResponse.setErrorMsg("Unknown proof step method");
        return unknownMethodResponse;
    }

    @POST
    @Path("/read")
    @Consumes(MediaType.MULTIPART_FORM_DATA)
    public ReadResponse readGivensAndToShowsFromFile(
            @FormDataParam("file") final InputStream inputStream,
            @FormDataParam("file") final FormDataContentDisposition contentDispositionHeader)
            throws IOException {

        ProofStreamReader reader = proofStreamReaderCreator.create();
        reader.load(inputStream);
        List<String> given = reader.getGiven();
        List<String> toShow = reader.getToShow();

        ReadResponse readResponse = new ReadResponse();
        readResponse.setGiven(given);
        readResponse.setToShow(toShow);

        return readResponse;
    }

    @POST
    @Path("/induction")
    public Response generateInductionSchema(SchemaRequest schemaRequest)
            throws FormulaParsingException, SchemaGeneratorException {

        String goal = schemaRequest.getGoal();

        SchemaResponse response = new SchemaResponse();
        response.setGoal(goal);

        Formula formula = formulaParser.fromString(goal);
        if (!(formula instanceof ForallFormula)) {
            return Response.status(422).entity(response).build();
        }

        InductionSchema schema = inductionSchemaGenerator.generateSchema((ForallFormula) formula);

        List<String> baseCaseToShow = new ArrayList<>();
        for (Formula bcts : schema.getBaseCaseToShow()) {
            baseCaseToShow.add(formulaStringBuilder.build(bcts));
        }
        String inductiveTerm = termStringBuilder.build(schema.getInductiveTerm());
        String indHyp = formulaStringBuilder.build(schema.getInductiveHypothesis());
        List<String> inductiveCaseToShow = new ArrayList<>();
        for (Formula icts : schema.getInductiveCaseToShow()) {
            inductiveCaseToShow.add(formulaStringBuilder.build(icts));
        }

        SchemaResponse.BaseCase baseCase = new SchemaResponse.BaseCase();
        baseCase.setToShow(baseCaseToShow);

        SchemaResponse.InductiveCase inductiveCase = new SchemaResponse.InductiveCase();
        inductiveCase.setArbitrary(inductiveTerm);
        inductiveCase.setHypothesis(indHyp);
        inductiveCase.setToShow(inductiveCaseToShow);

        response.setBaseCase(baseCase);
        response.setInductiveCase(inductiveCase);

        return Response.ok(response).build();
    }

}

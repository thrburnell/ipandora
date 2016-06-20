package com.ipandora.resources;

import com.ipandora.api.predicate.formula.EqualToFormula;
import com.ipandora.api.predicate.formula.ForallFormula;
import com.ipandora.api.predicate.formula.Formula;
import com.ipandora.api.predicate.function.FunctionDefinition;
import com.ipandora.api.predicate.function.FunctionPrototype;
import com.ipandora.api.predicate.function.FunctionPrototypeRequest;
import com.ipandora.api.predicate.induction.SchemaRequest;
import com.ipandora.api.predicate.induction.SchemaResponse;
import com.ipandora.api.predicate.proofstep.*;
import com.ipandora.api.predicate.read.ReadResponse;
import com.ipandora.api.predicate.term.Term;
import com.ipandora.api.predicate.term.Type;
import com.ipandora.api.predicate.term.TypeMismatchException;
import com.ipandora.api.predicate.term.Variable;
import com.ipandora.api.predicate.validate.ValidateFormulaRequest;
import com.ipandora.api.predicate.validate.ValidateFormulaResponse;
import com.ipandora.api.predicate.validate.ValidateFunctionRequest;
import com.ipandora.api.predicate.validate.ValidateFunctionResponse;
import com.ipandora.core.formula.FormulaParser;
import com.ipandora.core.formula.FormulaParsingException;
import com.ipandora.core.function.FunctionParser;
import com.ipandora.core.function.FunctionParsingException;
import com.ipandora.core.function.FunctionPrototypeBuildingVisitor;
import com.ipandora.core.induction.InductionSchema;
import com.ipandora.core.induction.InductionSchemaGenerator;
import com.ipandora.core.induction.SchemaGeneratorException;
import com.ipandora.core.proof.*;
import com.ipandora.core.term.TermParser;
import com.ipandora.core.term.TermParsingException;
import com.ipandora.core.term.TermTypeInferrer;
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
import java.util.Collections;
import java.util.List;

@Path("/predicate")
@Produces(MediaType.APPLICATION_JSON)
@Consumes(MediaType.APPLICATION_JSON)
public class PredicateResource {

    private static final int INVALID_REQUEST_CODE = 422;

    private final FormulaParser formulaParser;
    private final TermParser termParser;
    private final FunctionParser functionParser;
    private final ImpliesChecker impliesChecker;
    private final ArithmeticEqualityChecker equalityChecker;
    private final FunctionEqualityChecker functionEqualityChecker;
    private final ExhaustiveCaseChecker exhaustiveCaseChecker;
    private final ProofStreamReaderCreator proofStreamReaderCreator;
    private final InductionSchemaGenerator inductionSchemaGenerator;
    private final PrettyStringBuilder<Formula> formulaStringBuilder;
    private final PrettyStringBuilder<Term> termStringBuilder;
    private final TermTypeInferrer termTypeInferrer;
    private final FunctionPrototypeBuildingVisitor prototypeBuildingVisitor;

    public PredicateResource(FormulaParser formulaParser, TermParser termParser, FunctionParser functionParser,
                             ImpliesChecker impliesChecker,
                             ArithmeticEqualityChecker equalityChecker,
                             FunctionEqualityChecker functionEqualityChecker,
                             ExhaustiveCaseChecker exhaustiveCaseChecker,
                             ProofStreamReaderCreator proofStreamReaderCreator,
                             InductionSchemaGenerator inductionSchemaGenerator,
                             PrettyStringBuilder<Formula> formulaStringBuilder,
                             PrettyStringBuilder<Term> termStringBuilder,
                             TermTypeInferrer termTypeInferrer,
                             FunctionPrototypeBuildingVisitor prototypeBuildingVisitor) {
        this.formulaParser = formulaParser;
        this.termParser = termParser;
        this.functionParser = functionParser;
        this.impliesChecker = impliesChecker;
        this.equalityChecker = equalityChecker;
        this.functionEqualityChecker = functionEqualityChecker;
        this.exhaustiveCaseChecker = exhaustiveCaseChecker;
        this.proofStreamReaderCreator = proofStreamReaderCreator;
        this.inductionSchemaGenerator = inductionSchemaGenerator;
        this.formulaStringBuilder = formulaStringBuilder;
        this.termStringBuilder = termStringBuilder;
        this.termTypeInferrer = termTypeInferrer;
        this.prototypeBuildingVisitor = prototypeBuildingVisitor;
    }

    @POST
    @Path("/formula")
    public Response validateFormula(ValidateFormulaRequest validateRequest) {

        ValidateFormulaResponse validateResponse = new ValidateFormulaResponse();
        String formula = validateRequest.getFormula();
        if (formula == null) {
            validateResponse.setErrorMsg("Required formula missing");
            return invalidRequestResponse(validateResponse);
        }

        validateResponse.setFormula(formula);

        try {
            formulaParser.fromString(formula);
            validateResponse.setValid(true);
        } catch (FormulaParsingException e) {
            validateResponse.setValid(false);
            validateResponse.setErrorMsg("Invalid formula");
        }

        return Response.ok(validateResponse).build();
    }

    @POST
    @Path("/function")
    public Response validateFunction(ValidateFunctionRequest validateRequest) {

        ValidateFunctionResponse validateResponse = new ValidateFunctionResponse();

        String function = validateRequest.getFunction();
        if (function == null) {
            validateResponse.setErrorMsg("Required function missing");
        }

        validateResponse.setFunction(function);

        try {
            FunctionDefinition functionDefinition = functionParser.fromString(function);
            validateResponse.setValid(true);

            FunctionPrototype prototype = prototypeBuildingVisitor.visit(functionDefinition);
            FunctionPrototypeRequest prototypeRequest = getFunctionPrototypeRequest(prototype);
            validateResponse.setPrototype(prototypeRequest);
        } catch (FunctionParsingException e) {
            validateResponse.setValid(false);
            validateResponse.setErrorMsg("Invalid function");
        }

        return Response.ok(validateResponse).build();
    }

    @POST
    @Path("/step/case")
    public Response checkCasesExhaustive(ExhaustiveCasesRequest exhaustiveCasesRequest) {

        ExhaustiveCasesResponse response = new ExhaustiveCasesResponse();

        String first = exhaustiveCasesRequest.getFirst();
        String second = exhaustiveCasesRequest.getSecond();

        if (first == null) {
            response.setErrorMsg("Required first formula missing");
            return invalidRequestResponse(response);
        }
        if (second == null) {
            response.setErrorMsg("Required second formula missing");
            return invalidRequestResponse(response);
        }

        Formula firstFormula, secondFormula;
        try {
            firstFormula = formulaParser.fromString(first);
        } catch (FormulaParsingException e) {
            response.setErrorMsg("Invalid first formula");
            return invalidRequestResponse(response);
        }
        try {
            secondFormula = formulaParser.fromString(second);
        } catch (FormulaParsingException e) {
            response.setErrorMsg("Invalid second formula");
            return invalidRequestResponse(response);
        }

        boolean result;
        try {
            result = exhaustiveCaseChecker.check(firstFormula, secondFormula);
        } catch (ProofStepCheckException e) {
            response.setErrorMsg(e.getMessage());
            return invalidRequestResponse(response);
        }

        response.setFirst(first);
        response.setSecond(second);
        response.setExhaustive(result);
        return Response.ok(response).build();
    }

    @POST
    @Path("/step")
    public Response checkProofStep(StepRequest stepRequest) {

        String method = stepRequest.getMethod();

        switch (method) {
            case ProofStepMethods.LOGICAL_IMPLICATION:
                return checkProofStepLogicalImplication(stepRequest);

            case ProofStepMethods.ARITHMETIC:
                return checkProofStepArithmetic(stepRequest);

            case ProofStepMethods.FUNCTION_DEFINITION:
                return checkProofStepFunctionDefinition(stepRequest);

            case ProofStepMethods.INDUCTIVE_HYPOTHESIS:
                return checkProofStepInductiveHypothesis(stepRequest);
        }

        StepResponse unknownMethodResponse = new StepResponse();
        unknownMethodResponse.setMethod(method);
        unknownMethodResponse.setErrorMsg("Unknown proof step method");
        return invalidRequestResponse(unknownMethodResponse);
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
    public Response generateInductionSchema(SchemaRequest schemaRequest) {

        String goal = schemaRequest.getGoal();
        String varName = schemaRequest.getVariable();
        List<FunctionPrototypeRequest> functions = schemaRequest.getFunctions();
        if (functions == null) {
            functions = Collections.emptyList();
        }

        SchemaResponse response = new SchemaResponse();
        response.setGoal(goal);
        response.setVariable(varName);
        response.setFunctions(functions);

        List<FunctionPrototype> functionPrototypes;
        try {
            functionPrototypes = getFunctionPrototypes(functions);
        } catch (FormulaParsingException e) {
            response.setErrorMsg("Invalid function prototype: " + e.getMessage());
            return invalidRequestResponse(response);
        }

        Formula formula;
        try {
            formula = formulaParser.fromString(goal, functionPrototypes);
        } catch (FormulaParsingException e) {
            response.setErrorMsg("Invalid goal formula. Did you provide all correct function prototypes?");
            return invalidRequestResponse(response);
        }
        if (!(formula instanceof ForallFormula)) {
            response.setErrorMsg("Formula must be universally quantified.");
            return invalidRequestResponse(response);
        }

        Variable variable = Variable.withTypeNat(varName);
        InductionSchema schema;
        try {
            schema = inductionSchemaGenerator.generateSchema((ForallFormula) formula, variable);
        } catch (SchemaGeneratorException e) {
            response.setErrorMsg("Unable to generate schema: " + e.getMessage());
            return invalidRequestResponse(response);
        }

        List<String> baseCaseToShow = new ArrayList<>();
        for (Formula bcts : schema.getBaseCaseToShow()) {
            baseCaseToShow.add(formulaStringBuilder.build(bcts));
        }
        String indHyp = formulaStringBuilder.build(schema.getInductiveHypothesis());
        List<String> inductiveCaseToShow = new ArrayList<>();
        for (Formula icts : schema.getInductiveCaseToShow()) {
            inductiveCaseToShow.add(formulaStringBuilder.build(icts));
        }

        SchemaResponse.BaseCase baseCase = new SchemaResponse.BaseCase();
        baseCase.setToShow(baseCaseToShow);

        SchemaResponse.InductiveVariable inductiveVariable = new SchemaResponse.InductiveVariable();
        inductiveVariable.setName(termStringBuilder.build(schema.getInductiveTerm()));
        inductiveVariable.setDomain(schema.getInductiveTerm().getType().getName());
        
        SchemaResponse.InductiveCase inductiveCase = new SchemaResponse.InductiveCase();
        inductiveCase.setArbitrary(inductiveVariable);
        inductiveCase.setHypothesis(indHyp);
        inductiveCase.setToShow(inductiveCaseToShow);

        response.setBaseCase(baseCase);
        response.setInductiveCase(inductiveCase);

        return Response.ok(response).build();
    }

    private List<FunctionPrototype> getFunctionPrototypes(List<FunctionPrototypeRequest> prototypes)
            throws FormulaParsingException {

        List<FunctionPrototype> functionPrototypes = new ArrayList<>();

        for (FunctionPrototypeRequest prototype : prototypes) {

            String name = prototype.getName();
            ArrayList<Type> types = new ArrayList<>();
            Type returnType = getTypeOrThrow(prototype.getReturnType());

            for (String type : prototype.getArgTypes()) {
                types.add(getTypeOrThrow(type));
            }

            functionPrototypes.add(new FunctionPrototype(name, types, returnType));
        }

        return functionPrototypes;
    }

    @POST
    @Path("/equivalent")
    public Response areFormulasEquivalent(EquivalentRequest equivalentRequest) {

        EquivalentResponse response = new EquivalentResponse();

        String first = equivalentRequest.getFirst();
        String second = equivalentRequest.getSecond();
        response.setFirst(first);
        response.setSecond(second);

        if (first == null) {
            response.setErrorMsg("Required first missing");
            return invalidRequestResponse(response);
        }
        if (second == null) {
            response.setErrorMsg("Required second missing");
            return invalidRequestResponse(response);
        }

        Formula firstFormula;
        try {
            firstFormula = formulaParser.fromString(first);
        } catch (FormulaParsingException e) {
            response.setErrorMsg("Invalid first formula");
            return invalidRequestResponse(response);
        }

        Formula secondFormula;
        try {
            secondFormula = formulaParser.fromString(second);
        } catch (FormulaParsingException e) {
            response.setErrorMsg("Invalid second formula");
            return invalidRequestResponse(response);
        }

        boolean result;
        try {
            boolean lr = impliesChecker.check(Collections.singletonList(firstFormula), secondFormula);
            boolean rl = impliesChecker.check(Collections.singletonList(secondFormula), firstFormula);
            result = lr && rl;
        } catch (ProofStepCheckException e) {
            response.setErrorMsg(e.getMessage());
            return invalidRequestResponse(response);
        }

        response.setEquivalent(result);

        return Response.ok(response).build();
    }

    @POST
    @Path("/equalstructure")
    public Response areTermsEqualStructure(TermEqualStructureRequest equalStructureRequest) {

        TermEqualStructureResponse response = new TermEqualStructureResponse();

        String first = equalStructureRequest.getFirst();
        String second = equalStructureRequest.getSecond();
        response.setFirst(first);
        response.setSecond(second);

        if (first == null) {
            response.setErrorMsg("Required first missing");
            return invalidRequestResponse(response);
        }
        if (second == null) {
            response.setErrorMsg("Required second missing");
            return invalidRequestResponse(response);
        }

        Term firstTerm;
        try {
            firstTerm = termParser.fromString(first);
        } catch (TermParsingException e) {
            response.setErrorMsg("Invalid first term: " + first);
            return invalidRequestResponse(response);
        }

        Term secondTerm;
        try {
            secondTerm = termParser.fromString(second);
        } catch (TermParsingException e) {
            response.setErrorMsg("Invalid second term: " + second);
            return invalidRequestResponse(response);
        }

        boolean equal = firstTerm.equals(secondTerm);
        response.setEqual(equal);

        return Response.ok(response).build();
    }

    private FunctionPrototypeRequest getFunctionPrototypeRequest(FunctionPrototype prototype) {
        FunctionPrototypeRequest functionPrototypeRequest = new FunctionPrototypeRequest();

        functionPrototypeRequest.setName(prototype.getName());

        List<String> argTypes = new ArrayList<>();
        for (Type type : prototype.getArgTypes()) {
            argTypes.add(type.getName());
        }

        functionPrototypeRequest.setArgTypes(argTypes);
        functionPrototypeRequest.setReturnType(prototype.getReturnType().getName());

        return functionPrototypeRequest;
    }

    private Type getTypeOrThrow(String type) throws FormulaParsingException {

        for (Type t : Type.values()) {
            if (t.getName().equals(type)) {
                return t;
            }
        }
        throw new FormulaParsingException("Unknown type: " + type);
    }

    private Response checkProofStepLogicalImplication(StepRequest stepRequest) {
        assert stepRequest.getMethod().equals(ProofStepMethods.LOGICAL_IMPLICATION);

        StepResponse stepResponse = new StepResponse();
        stepResponse.setMethod(ProofStepMethods.LOGICAL_IMPLICATION);

        List<String> assumptions = stepRequest.getAssumptions();
        if (assumptions == null) {
            stepResponse.setErrorMsg("Required assumptions missing");
            return invalidRequestResponse(stepResponse);
        }

        String goal = stepRequest.getGoal();
        if (goal == null) {
            stepResponse.setErrorMsg("Required goal missing");
            return invalidRequestResponse(stepResponse);
        }

        List<FunctionPrototypeRequest> prototypes = stepRequest.getFunctions();
        if (prototypes == null) {
            prototypes = new ArrayList<>();
        }

        List<FunctionPrototype> functionPrototypes;
        try {
            functionPrototypes = getFunctionPrototypes(prototypes);
        } catch (FormulaParsingException e) {
            stepResponse.setErrorMsg("Invalid function prototype: " + e.getMessage());
            return invalidRequestResponse(stepResponse);
        }

        String arbitrary = stepRequest.getArbitrary();
        stepResponse.setArbitrary(arbitrary);

        List<Formula> assumptionFormulas = new ArrayList<>();
        for (String assumption : assumptions) {
            try {
                Formula f = formulaParser.fromStringWithTypeChecking(assumption, functionPrototypes);
                if (arbitrary != null) {
                    f = new ForallFormula(new Variable(arbitrary), f);
                }
                assumptionFormulas.add(f);
            } catch (FormulaParsingException e) {
                stepResponse.setErrorMsg("Invalid assumption formula: " + assumption);
                return invalidRequestResponse(stepResponse);
            }
        }

        Formula goalFormula;
        try {
            goalFormula = formulaParser.fromStringWithTypeChecking(goal, functionPrototypes);
        } catch (FormulaParsingException e) {
            stepResponse.setErrorMsg("Invalid goal formula: " + goal);
            return invalidRequestResponse(stepResponse);
        }

        boolean result;
        try {
            result = impliesChecker.check(assumptionFormulas, goalFormula);
        } catch (ProofStepCheckException e) {
            stepResponse.setErrorMsg(e.getMessage());
            return invalidRequestResponse(stepResponse);
        }

        stepResponse.setGoal(goal);
        stepResponse.setAssumptions(assumptions);
        stepResponse.setValid(result);

        if (!result) {
            stepResponse.setErrorMsg("Error messages not yet implemented.");
        }

        return Response.ok(stepResponse).build();
    }

    private Response checkProofStepArithmetic(StepRequest stepRequest) {
        assert stepRequest.getMethod().equals(ProofStepMethods.ARITHMETIC);

        StepResponse stepResponse = new StepResponse();
        stepResponse.setMethod(ProofStepMethods.ARITHMETIC);

        String goal = stepRequest.getGoal();
        if (goal == null) {
            stepResponse.setErrorMsg("Required goal missing");
            return invalidRequestResponse(stepResponse);
        }

        String from = stepRequest.getFrom();
        if (from == null) {
            stepResponse.setErrorMsg("Required from missing");
            return invalidRequestResponse(stepResponse);
        }

        Term fromTerm;
        try {
            fromTerm = termParser.fromString(from);
            termTypeInferrer.infer(fromTerm);
        } catch (TermParsingException | TypeMismatchException e) {
            stepResponse.setErrorMsg("Invalid from term: " + from);
            return invalidRequestResponse(stepResponse);
        }

        Term goalTerm;
        try {
            goalTerm = termParser.fromString(goal);
            termTypeInferrer.infer(goalTerm);
        } catch (TermParsingException | TypeMismatchException e) {
            stepResponse.setErrorMsg("Invalid goal term: " + goal);
            return invalidRequestResponse(stepResponse);
        }

        boolean result;
        try {
            result = equalityChecker.check(fromTerm, goalTerm);
        } catch (ProofStepCheckException e) {
            stepResponse.setErrorMsg(e.getMessage());
            return invalidRequestResponse(stepResponse);
        }

        stepResponse.setGoal(goal);
        stepResponse.setFrom(from);
        stepResponse.setValid(result);

        return Response.ok(stepResponse).build();
    }

    private Response checkProofStepFunctionDefinition(StepRequest stepRequest) {
        assert stepRequest.getMethod().equals(ProofStepMethods.FUNCTION_DEFINITION);

        StepResponse stepResponse = new StepResponse();
        stepResponse.setMethod(ProofStepMethods.FUNCTION_DEFINITION);

        String goal = stepRequest.getGoal();
        if (goal == null) {
            stepResponse.setErrorMsg("Required goal missing");
            return invalidRequestResponse(stepResponse);
        }

        String from = stepRequest.getFrom();
        if (from == null) {
            stepResponse.setErrorMsg("Required from missing");
            return invalidRequestResponse(stepResponse);
        }

        String function = stepRequest.getFunction();
        if (function == null) {
            stepResponse.setErrorMsg("Required function missing");
            return invalidRequestResponse(stepResponse);
        }

        List<FunctionPrototypeRequest> prototypes = stepRequest.getFunctions();
        if (prototypes == null) {
            prototypes = new ArrayList<>();
        }

        List<FunctionPrototype> functionPrototypes;
        try {
            functionPrototypes = getFunctionPrototypes(prototypes);
        } catch (FormulaParsingException e) {
            stepResponse.setErrorMsg("Invalid function prototype: " + e.getMessage());
            return invalidRequestResponse(stepResponse);
        }

        Term fromTerm;
        try {
            fromTerm = termParser.fromString(from, functionPrototypes);
            termTypeInferrer.infer(fromTerm);
        } catch (TermParsingException | TypeMismatchException e) {
            stepResponse.setErrorMsg("Invalid from term: " + from);
            return invalidRequestResponse(stepResponse);
        }

        Term goalTerm;
        try {
            goalTerm = termParser.fromString(goal, functionPrototypes);
            termTypeInferrer.infer(goalTerm);
        } catch (TermParsingException | TypeMismatchException e) {
            stepResponse.setErrorMsg("Invalid goal term: " + goal);
            return invalidRequestResponse(stepResponse);
        }

        FunctionDefinition functionDefinition;
        try {
            functionDefinition = functionParser.fromStringWithTypeChecking(function, functionPrototypes);
        } catch (FunctionParsingException e) {
            stepResponse.setErrorMsg("Invalid function.");
            return invalidRequestResponse(function);
        }

        boolean result;
        try {
            result = functionEqualityChecker.check(fromTerm, goalTerm, functionDefinition);
        } catch (ProofStepCheckException e) {
            stepResponse.setErrorMsg(e.getMessage());
            return invalidRequestResponse(stepResponse);
        }

        stepResponse.setFrom(from);
        stepResponse.setGoal(goal);
        stepResponse.setFunction(function);
        stepResponse.setFunctions(prototypes);
        stepResponse.setValid(result);

        return Response.ok(stepResponse).build();
    }

    private Response checkProofStepInductiveHypothesis(StepRequest stepRequest) {

        StepResponse stepResponse = new StepResponse();

        String goal = stepRequest.getGoal();
        String from = stepRequest.getFrom();
        String inductiveHypothesis = stepRequest.getInductiveHypothesis();
        String arbitrary = stepRequest.getArbitrary();

        List<FunctionPrototypeRequest> prototypes = stepRequest.getFunctions();
        if (prototypes == null) {
            prototypes = new ArrayList<>();
        }

        List<FunctionPrototype> functionPrototypes;
        try {
            functionPrototypes = getFunctionPrototypes(prototypes);
        } catch (FormulaParsingException e) {
            stepResponse.setErrorMsg("Invalid function prototype: " + e.getMessage());
            return invalidRequestResponse(stepResponse);
        }

        Term fromTerm;
        try {
            fromTerm = termParser.fromString(from, functionPrototypes);
            termTypeInferrer.infer(fromTerm);
        } catch (TermParsingException | TypeMismatchException e) {
            stepResponse.setErrorMsg("Invalid from term: " + from);
            return invalidRequestResponse(stepResponse);
        }

        Term goalTerm;
        try {
            goalTerm = termParser.fromString(goal, functionPrototypes);
            termTypeInferrer.infer(goalTerm);
        } catch (TermParsingException | TypeMismatchException e) {
            stepResponse.setErrorMsg("Invalid goal term: " + goal);
            return invalidRequestResponse(stepResponse);
        }

        Formula indHypFormula;
        try {
            indHypFormula = formulaParser.fromStringWithTypeChecking(
                    String.format("\\FORALL %s in Nat. %s", arbitrary, inductiveHypothesis), functionPrototypes);
        } catch (FormulaParsingException e) {
            stepResponse.setErrorMsg("Invalid inductive hypothesis: " + goal);
            return invalidRequestResponse(stepResponse);
        }

        boolean result;
        try {
            result = impliesChecker.check(Collections.singletonList(indHypFormula),
                    new EqualToFormula(fromTerm, goalTerm));
        } catch (ProofStepCheckException e) {
            stepResponse.setErrorMsg(e.getMessage());
            return invalidRequestResponse(stepResponse);
        }

        stepResponse.setGoal(goal);
        stepResponse.setFrom(from);
        stepResponse.setInductiveHypothesis(inductiveHypothesis);
        stepRequest.setArbitrary(arbitrary);
        stepResponse.setValid(result);

        if (!result) {
            stepResponse.setErrorMsg("Error messages not yet implemented.");
        }

        return Response.ok(stepResponse).build();
    }

    private Response invalidRequestResponse(Object entity) {
        return Response.status(INVALID_REQUEST_CODE).entity(entity).build();
    }

}

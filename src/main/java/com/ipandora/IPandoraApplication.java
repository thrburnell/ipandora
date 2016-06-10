package com.ipandora;

import com.ipandora.core.formula.*;
import com.ipandora.core.function.ANTLRFunctionParser;
import com.ipandora.core.function.FunctionDefinitionEncoderImpl;
import com.ipandora.core.function.FunctionPrototypeBuildingVisitor;
import com.ipandora.core.function.FunctionTypeChecker;
import com.ipandora.core.induction.MathematicalInductionSchemaGenerator;
import com.ipandora.core.proof.ProofStreamReaderCreator;
import com.ipandora.core.term.*;
import com.ipandora.core.util.EnvironmentVariableProviderImpl;
import com.ipandora.core.util.ProcessExecutorImpl;
import com.ipandora.core.z3.*;
import com.ipandora.resources.PredicateResource;
import io.dropwizard.Application;
import io.dropwizard.bundles.assets.ConfiguredAssetsBundle;
import io.dropwizard.configuration.EnvironmentVariableSubstitutor;
import io.dropwizard.configuration.SubstitutingSourceProvider;
import io.dropwizard.setup.Bootstrap;
import io.dropwizard.setup.Environment;
import org.glassfish.jersey.media.multipart.MultiPartFeature;

public class IPandoraApplication extends Application<IPandoraConfiguration> {

    public static void main(String[] args) throws Exception {
        new IPandoraApplication().run(args);
    }

    @Override
    public void initialize(Bootstrap<IPandoraConfiguration> bootstrap) {
        bootstrap.setConfigurationSourceProvider(
                new SubstitutingSourceProvider(bootstrap.getConfigurationSourceProvider(),
                        new EnvironmentVariableSubstitutor()));

        bootstrap.addBundle(new ConfiguredAssetsBundle("/public", "/", "index.html"));
    }

    @Override
    public void run(IPandoraConfiguration IPandoraConfiguration,
                    Environment environment) throws Exception {

        // Type checkers
        TermTypeChecker termTypeChecker = new TermTypeChecker();
        FormulaTypeChecker formulaTypeChecker = new FormulaTypeChecker(termTypeChecker);
        FunctionTypeChecker functionTypeChecker = new FunctionTypeChecker(termTypeChecker, formulaTypeChecker);
        TermTypeInferrer termTypeInferrer = new TermTypeInferrer();

        // Parsers
        ANTLRFormulaParser formulaParser = new ANTLRFormulaParser(formulaTypeChecker);
        ANTLRTermParser termParser = new ANTLRTermParser(termTypeChecker);
        ANTLRFunctionParser functionParser = new ANTLRFunctionParser(functionTypeChecker);

        // Z3 checkers
        Z3ImpliesChecker impliesChecker = new Z3ImpliesChecker(
                new SMTCodeGeneratorImpl(new SMTGeneratingFormulaVisitorCreator()),
                new Z3ClientImpl(new ProcessExecutorImpl(), new EnvironmentVariableProviderImpl()),
                new FormulaConjunctionReducer());

        Z3ArithmeticEqualityChecker equalityChecker = new Z3ArithmeticEqualityChecker(
                new SMTCodeGeneratorImpl(new SMTGeneratingFormulaVisitorCreator()),
                new Z3ClientImpl(new ProcessExecutorImpl(), new EnvironmentVariableProviderImpl()));

        Z3FunctionEqualityChecker functionEqualityChecker = new Z3FunctionEqualityChecker(
                new SMTCodeGeneratorImpl(new SMTGeneratingFormulaVisitorCreator()),
                new Z3ClientImpl(new ProcessExecutorImpl(), new EnvironmentVariableProviderImpl()),
                new FunctionDefinitionEncoderImpl(new FormulaConjunctionReducer()));

        Z3ExhaustiveCaseChecker exhaustiveCaseChecker = new Z3ExhaustiveCaseChecker(
                new SMTCodeGeneratorImpl(new SMTGeneratingFormulaVisitorCreator()),
                new Z3ClientImpl(new ProcessExecutorImpl(), new EnvironmentVariableProviderImpl()));

        // Schema generator
        MathematicalInductionSchemaGenerator inductionSchemaGenerator = new MathematicalInductionSchemaGenerator(
                new TermStringBuilder(), new TermSubstitutor());

        // String builders
        FormulaStringBuilder formulaStringBuilder = new FormulaStringBuilder(new TermStringBuilder());
        TermStringBuilder termStringBuilder = new TermStringBuilder();

        // Utils
        ProofStreamReaderCreator proofStreamReaderCreator = new ProofStreamReaderCreator();

        FunctionPrototypeBuildingVisitor prototypeBuildingVisitor = new FunctionPrototypeBuildingVisitor();

        // Resources
        PredicateResource resource = new PredicateResource(formulaParser, termParser, functionParser, impliesChecker,
                equalityChecker, functionEqualityChecker, exhaustiveCaseChecker, proofStreamReaderCreator,
                inductionSchemaGenerator, formulaStringBuilder, termStringBuilder, termTypeInferrer,
                prototypeBuildingVisitor);

        environment.jersey().register(resource);
        environment.jersey().register(MultiPartFeature.class);
    }
}

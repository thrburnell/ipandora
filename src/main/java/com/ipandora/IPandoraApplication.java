package com.ipandora;

import com.ipandora.core.formula.*;
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
        
        FormulaTypeChecker formulaTypeChecker = new FormulaTypeChecker(new TermTypeChecker());
        ANTLRFormulaParser formulaParser = new ANTLRFormulaParser(formulaTypeChecker);

        Z3ImpliesChecker impliesChecker = new Z3ImpliesChecker(
                new SMTCodeGeneratorImpl(new SMTGeneratingFormulaVisitorCreator()),
                new Z3ClientImpl(new ProcessExecutorImpl(), new EnvironmentVariableProviderImpl()),
                new FormulaConjunctionReducer());

        Z3ArithmeticEqualityChecker equalityChecker = new Z3ArithmeticEqualityChecker(
                new SMTCodeGeneratorImpl(new SMTGeneratingFormulaVisitorCreator()),
                new Z3ClientImpl(new ProcessExecutorImpl(), new EnvironmentVariableProviderImpl()));

        ProofStreamReaderCreator proofStreamReaderCreator = new ProofStreamReaderCreator();

        MathematicalInductionSchemaGenerator inductionSchemaGenerator = new MathematicalInductionSchemaGenerator(
                new TermStringBuilder(), new TermSubstitutor());

        FormulaStringBuilder formulaStringBuilder = new FormulaStringBuilder(new TermStringBuilder());
        TermStringBuilder termStringBuilder = new TermStringBuilder();

        ANTLRTermParser termParser = new ANTLRTermParser(new TermTypeChecker());

        TermTypeInferrer termTypeInferrer = new TermTypeInferrer();

        PredicateResource resource = new PredicateResource(formulaParser, termParser, impliesChecker, equalityChecker,
                proofStreamReaderCreator, inductionSchemaGenerator, formulaStringBuilder, termStringBuilder,
                termTypeInferrer);
        environment.jersey().register(resource);

        environment.jersey().register(MultiPartFeature.class);
    }
}

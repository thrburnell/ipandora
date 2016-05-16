package com.ipandora;

import com.ipandora.core.formula.ANTLRFormulaParser;
import com.ipandora.core.formula.FormulaBuildingVisitor;
import com.ipandora.core.formula.FormulaConjunctionReducer;
import com.ipandora.core.formula.TypeCheckAnalyser;
import com.ipandora.core.proof.ProofStreamReaderCreator;
import com.ipandora.core.term.SymbolTableCreator;
import com.ipandora.core.term.TermBuildingVisitor;
import com.ipandora.core.term.TermTypeChecker;
import com.ipandora.core.util.EnvironmentVariableProviderImpl;
import com.ipandora.core.util.ProcessExecutorImpl;
import com.ipandora.core.z3.SMTCodeGeneratorImpl;
import com.ipandora.core.z3.SMTGeneratingFormulaVisitorCreator;
import com.ipandora.core.z3.Z3ClientImpl;
import com.ipandora.core.z3.Z3ImpliesChecker;
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

        SymbolTableCreator symbolTableCreator = new SymbolTableCreator();
        FormulaBuildingVisitor formulaBuildingVisitor = new FormulaBuildingVisitor(
                new TermBuildingVisitor(symbolTableCreator));
        TypeCheckAnalyser typeCheckAnalyser = new TypeCheckAnalyser(new TermTypeChecker());

        ANTLRFormulaParser formulaParser = new ANTLRFormulaParser(formulaBuildingVisitor, typeCheckAnalyser);

        Z3ImpliesChecker impliesChecker = new Z3ImpliesChecker(
                new SMTCodeGeneratorImpl(new SMTGeneratingFormulaVisitorCreator()),
                new Z3ClientImpl(new ProcessExecutorImpl(), new EnvironmentVariableProviderImpl()),
                new FormulaConjunctionReducer());

        ProofStreamReaderCreator proofStreamReaderCreator = new ProofStreamReaderCreator();

        PredicateResource resource = new PredicateResource(formulaParser, impliesChecker, proofStreamReaderCreator);
        environment.jersey().register(resource);

        environment.jersey().register(MultiPartFeature.class);
    }
}

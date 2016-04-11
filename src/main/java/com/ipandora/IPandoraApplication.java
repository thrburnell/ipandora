package com.ipandora;

import com.ipandora.core.formula.FormulaConjunctionReducer;
import com.ipandora.core.formula.FormulaParser;
import com.ipandora.core.util.ProcessExecutorImpl;
import com.ipandora.core.z3.SMTCodeGeneratorImpl;
import com.ipandora.core.z3.SMTGeneratingFormulaVisitorImpl;
import com.ipandora.core.z3.Z3ClientImpl;
import com.ipandora.core.z3.Z3ImpliesChecker;
import com.ipandora.resources.PredicateResource;
import io.dropwizard.Application;
import io.dropwizard.configuration.EnvironmentVariableSubstitutor;
import io.dropwizard.configuration.SubstitutingSourceProvider;
import io.dropwizard.setup.Bootstrap;
import io.dropwizard.setup.Environment;

public class IPandoraApplication extends Application<IPandoraConfiguration> {

    public static void main(String[] args) throws Exception {
        new IPandoraApplication().run(args);
    }

    @Override
    public void initialize(Bootstrap<IPandoraConfiguration> bootstrap) {
        bootstrap.setConfigurationSourceProvider(
                new SubstitutingSourceProvider(bootstrap.getConfigurationSourceProvider(),
                        new EnvironmentVariableSubstitutor()));
    }

    @Override
    public void run(IPandoraConfiguration IPandoraConfiguration,
                    Environment environment) throws Exception {

        FormulaParser formulaParser = new FormulaParser();

        Z3ImpliesChecker impliesChecker = new Z3ImpliesChecker(
                new SMTCodeGeneratorImpl(new SMTGeneratingFormulaVisitorImpl()),
                new Z3ClientImpl(new ProcessExecutorImpl()), new FormulaConjunctionReducer());

        PredicateResource resource = new PredicateResource(formulaParser, impliesChecker);
        environment.jersey().register(resource);
    }
}

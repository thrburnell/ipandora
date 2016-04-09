package com.ipandora;

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

        PredicateResource resource = new PredicateResource();
        environment.jersey().register(resource);
    }
}

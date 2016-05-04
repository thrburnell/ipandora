package com.ipandora.core.util;

public class EnvironmentVariableProviderImpl implements EnvironmentVariableProvider {

    @Override
    public String getValue(String key) {
        return System.getenv(key);
    }

}

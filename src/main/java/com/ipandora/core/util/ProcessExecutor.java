package com.ipandora.core.util;

import java.io.IOException;

public interface ProcessExecutor {

    String execute(String stdin, int timeoutSeconds, String... command) throws IOException, ProcessTimeoutException;

}

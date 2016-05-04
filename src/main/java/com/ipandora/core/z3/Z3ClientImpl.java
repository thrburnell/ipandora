package com.ipandora.core.z3;

import com.ipandora.core.util.EnvironmentVariableProvider;
import com.ipandora.core.util.ProcessExecutor;
import com.ipandora.core.util.ProcessTimeoutException;

import java.io.IOException;

public class Z3ClientImpl implements Z3Client {

    public static final String Z3_BIN_PATH_VARNAME = "Z3_BINARY_PATH";
    private static int Z3_TIMEOUT_SECONDS = 5;

    private final ProcessExecutor processExecutor;
    private final EnvironmentVariableProvider environmentVariableProvider;

    public Z3ClientImpl(ProcessExecutor processExecutor, EnvironmentVariableProvider environmentVariableProvider) {
        this.processExecutor = processExecutor;
        this.environmentVariableProvider = environmentVariableProvider;
    }

    @Override
    public boolean isSat(String program) throws IOException, Z3UnrecognisableOutputException, ProcessTimeoutException {

        try {
            String z3BinaryPath = environmentVariableProvider.getValue(Z3_BIN_PATH_VARNAME);

            if (z3BinaryPath == null) {
                throw new Z3BinaryNotFoundException(
                        String.format("Couldn't find Z3 binary (%s not set).", Z3_BIN_PATH_VARNAME));
            }

            String output = processExecutor.execute(program, Z3_TIMEOUT_SECONDS, z3BinaryPath, "-smt2", "-in");;

            if (output.startsWith("sat")) {
                return true;
            } else if (output.startsWith("unsat")) {
                return false;
            } else {
                throw new Z3UnrecognisableOutputException("Z3 output didn't begin with sat or unsat. " +
                        "Did the given program ask for (check-sat)?");
            }

        } catch (ProcessTimeoutException e) {
            e.printStackTrace();
            throw e;
        }
    }

}

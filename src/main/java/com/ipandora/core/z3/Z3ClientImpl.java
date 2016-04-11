package com.ipandora.core.z3;

import com.ipandora.core.util.ProcessExecutor;
import com.ipandora.core.util.ProcessTimeoutException;

import java.io.IOException;

public class Z3ClientImpl implements Z3Client {

    private static int Z3_TIMEOUT_SECONDS = 5;

    private final ProcessExecutor processExecutor;

    public Z3ClientImpl(ProcessExecutor processExecutor) {
        this.processExecutor = processExecutor;
    }

    @Override
    public boolean isSat(String program) throws IOException, Z3UnrecognisableOutputException, ProcessTimeoutException {

        try {
            String output = processExecutor.execute(program, Z3_TIMEOUT_SECONDS, "z3", "-smt2", "-in");;

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

package com.ipandora.core.z3;

import com.ipandora.core.util.ProcessTimeoutException;

import java.io.IOException;

public interface Z3Client {

    boolean isSat(String program) throws IOException, Z3UnrecognisableOutputException, ProcessTimeoutException, Z3UnknownException;

}

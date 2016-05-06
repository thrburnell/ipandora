package com.ipandora.core.proof;

import java.io.IOException;
import java.io.InputStream;
import java.util.List;

public interface ProofStreamReader {

    void load(InputStream is) throws IOException;
    List<String> getGiven();
    List<String> getToShow();

}

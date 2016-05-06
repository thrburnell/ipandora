package com.ipandora.core.proof;

import com.ipandora.core.util.BufferedReaderGenerator;
import com.ipandora.core.util.BufferedReaderGeneratorImpl;
import com.ipandora.core.util.Creator;

public class ProofStreamReaderCreator implements Creator<ProofStreamReader> {

    @Override
    public ProofStreamReader create() {
        BufferedReaderGenerator bufferedReaderGenerator = new BufferedReaderGeneratorImpl();
        return new ProofStreamReaderImpl(bufferedReaderGenerator);
    }

}

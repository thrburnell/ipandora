package com.ipandora.core.util;

import java.io.BufferedReader;
import java.io.InputStream;
import java.io.InputStreamReader;

public class BufferedReaderGeneratorImpl implements BufferedReaderGenerator {

    @Override
    public BufferedReader fromInputStream(InputStream is) {
        InputStreamReader isr = new InputStreamReader(is);
        return new BufferedReader(isr);
    }

}

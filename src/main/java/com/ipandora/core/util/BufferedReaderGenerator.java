package com.ipandora.core.util;

import java.io.BufferedReader;
import java.io.InputStream;

public interface BufferedReaderGenerator {

    BufferedReader fromInputStream(InputStream is);

}

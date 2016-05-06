package com.ipandora.core.proof;

import com.ipandora.core.util.BufferedReaderGenerator;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

public class ProofStreamReaderImpl implements ProofStreamReader {

    private final static String GIVEN_HEADER = "# GIVEN";
    private final static String TO_SHOW_HEADER = "# TO SHOW";

    private final List<String> given = new ArrayList<>();
    private final List<String> toShow = new ArrayList<>();

    private final BufferedReaderGenerator bufferedReaderGenerator;

    public ProofStreamReaderImpl(BufferedReaderGenerator bufferedReaderGenerator) {
        this.bufferedReaderGenerator = bufferedReaderGenerator;
    }

    @Override
    public void load(InputStream is) throws IOException {

        BufferedReader br = bufferedReaderGenerator.fromInputStream(is);

        String line;
        boolean givenMode = false, toShowMode = false;
        while ((line = br.readLine()) != null) {

            line = line.trim();
            if (!line.isEmpty()) {
                if (line.equals(GIVEN_HEADER)) {
                    givenMode = true;
                    toShowMode = false;
                } else if (line.equals(TO_SHOW_HEADER)) {
                    givenMode = false;
                    toShowMode = true;
                } else if (givenMode) {
                    given.add(line);
                } else if (toShowMode) {
                    toShow.add(line);
                }
            }
        }
    }

    @Override
    public List<String> getGiven() {
        return new ArrayList<>(given);
    }

    @Override
    public List<String> getToShow() {
        return new ArrayList<>(toShow);
    }

}

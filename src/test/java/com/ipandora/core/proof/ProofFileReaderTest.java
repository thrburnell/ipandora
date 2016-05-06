package com.ipandora.core.proof;

import com.ipandora.core.util.BufferedReaderGenerator;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.mockito.Mock;
import org.mockito.runners.MockitoJUnitRunner;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.util.List;

import static org.assertj.core.api.Assertions.assertThat;
import static org.mockito.Matchers.any;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

@RunWith(MockitoJUnitRunner.class)
public class ProofFileReaderTest {

    @Mock
    private BufferedReaderGenerator bufferedReaderGenerator;

    @Mock
    private BufferedReader loadedBufferedReader;

    @Mock
    private BufferedReader emptyBufferedReader;

    @Before
    public void before() throws IOException {
        loadBufferedReader();
        when(emptyBufferedReader.readLine()).thenReturn(null);
    }

    private void loadBufferedReader() throws IOException {
        when(loadedBufferedReader.readLine())
                .thenReturn("# GIVEN")
                .thenReturn("A")
                .thenReturn("B")
                .thenReturn("C")
                .thenReturn("# TO SHOW")
                .thenReturn("D")
                .thenReturn("E")
                .thenReturn(null);
    }

    @Test
    public void loadShouldRequestABufferedReaderFromInputStream() throws IOException {

        when(bufferedReaderGenerator.fromInputStream(any(InputStream.class))).thenReturn(emptyBufferedReader);

        InputStream inputStream = getInputStream();
        ProofStreamReaderImpl proofStreamReader = new ProofStreamReaderImpl(bufferedReaderGenerator);
        proofStreamReader.load(inputStream);

        verify(bufferedReaderGenerator).fromInputStream(inputStream);
    }

    @Test
    public void getGivenShouldReturnAllGivensFromStream() throws IOException {

        when(bufferedReaderGenerator.fromInputStream(any(InputStream.class))).thenReturn(loadedBufferedReader);

        ProofStreamReaderImpl proofStreamReader = new ProofStreamReaderImpl(bufferedReaderGenerator);
        proofStreamReader.load(getInputStream());
        List<String> given = proofStreamReader.getGiven();

        assertThat(given).hasSize(3);
        assertThat(given).contains("A").contains("B").contains("C");
    }

    @Test
    public void getToShowShouldReturnAllToShowsFromStream() throws IOException {

        when(bufferedReaderGenerator.fromInputStream(any(InputStream.class))).thenReturn(loadedBufferedReader);

        ProofStreamReaderImpl proofStreamReader = new ProofStreamReaderImpl(bufferedReaderGenerator);
        proofStreamReader.load(getInputStream());
        List<String> toShow = proofStreamReader.getToShow();

        assertThat(toShow).hasSize(2);
        assertThat(toShow).contains("D").contains("E");
    }

    private InputStream getInputStream() {
        return new InputStream() {
            @Override
            public int read() throws IOException {
                return 0;
            }
        };
    }

}
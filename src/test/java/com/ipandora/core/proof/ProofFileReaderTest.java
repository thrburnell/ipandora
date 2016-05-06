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
    private BufferedReaderGenerator mockBufferedReaderGenerator;

    @Mock
    private BufferedReader mockLoadedBufferedReader;

    @Mock
    private BufferedReader mockEmptyBufferedReader;

    @Before
    public void before() throws IOException {
        loadBufferedReader();
        when(mockEmptyBufferedReader.readLine()).thenReturn(null);
    }

    private void loadBufferedReader() throws IOException {
        when(mockLoadedBufferedReader.readLine())
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

        when(mockBufferedReaderGenerator.fromInputStream(any(InputStream.class))).thenReturn(mockEmptyBufferedReader);

        InputStream inputStream = getInputStream();
        ProofStreamReaderImpl proofStreamReader = new ProofStreamReaderImpl(mockBufferedReaderGenerator);
        proofStreamReader.load(inputStream);

        verify(mockBufferedReaderGenerator).fromInputStream(inputStream);
    }

    @Test
    public void getGivenShouldReturnAllGivensFromStream() throws IOException {

        when(mockBufferedReaderGenerator.fromInputStream(any(InputStream.class))).thenReturn(mockLoadedBufferedReader);

        ProofStreamReaderImpl proofStreamReader = new ProofStreamReaderImpl(mockBufferedReaderGenerator);
        proofStreamReader.load(getInputStream());
        List<String> given = proofStreamReader.getGiven();

        assertThat(given).hasSize(3);
        assertThat(given).contains("A").contains("B").contains("C");
    }

    @Test
    public void getToShowShouldReturnAllToShowsFromStream() throws IOException {

        when(mockBufferedReaderGenerator.fromInputStream(any(InputStream.class))).thenReturn(mockLoadedBufferedReader);

        ProofStreamReaderImpl proofStreamReader = new ProofStreamReaderImpl(mockBufferedReaderGenerator);
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
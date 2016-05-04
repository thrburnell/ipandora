package com.ipandora.core.z3;

import com.ipandora.core.util.EnvironmentVariableProvider;
import com.ipandora.core.util.ProcessExecutor;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.mockito.Matchers;
import org.mockito.Mock;
import org.mockito.runners.MockitoJUnitRunner;

import static org.assertj.core.api.Assertions.assertThat;
import static org.mockito.Matchers.anyInt;
import static org.mockito.Matchers.anyString;
import static org.mockito.Mockito.when;

@RunWith(MockitoJUnitRunner.class)
public class Z3ClientImplTest {

    @Mock
    private ProcessExecutor processExecutor;

    @Mock
    private EnvironmentVariableProvider environmentVariableProvider;

    @Before
    public void before() {
        when(environmentVariableProvider.getValue(anyString())).thenReturn("DUMMY_NON_NULL_VALUE");
    }

    @Test
    public void isSatReturnsTrueWhenOutputBeginsWithSat() throws Exception {
        Z3Client z3Client = new Z3ClientImpl(processExecutor, environmentVariableProvider);

        when(processExecutor.execute(anyString(), anyInt(), Matchers.<String>anyVararg()))
                .thenReturn("sat and some more output");

        boolean isSat = z3Client.isSat("Demo program");

        assertThat(isSat).isTrue();
    }

    @Test
    public void isSatReturnsFalseWhenOutputBeginsWithUnsat() throws Exception {
        Z3Client z3Client = new Z3ClientImpl(processExecutor, environmentVariableProvider);

        when(processExecutor.execute(anyString(), anyInt(), Matchers.<String>anyVararg()))
                .thenReturn("unsat and some more output");

        boolean isSat = z3Client.isSat("Demo program");

        assertThat(isSat).isFalse();
    }

    @Test(expected = Z3UnrecognisableOutputException.class)
    public void isSatThrowsUnrecognisableOutputExceptionWhenOutputDoesntBeginWithSatOrUnsat() throws Exception {
        Z3Client z3Client = new Z3ClientImpl(processExecutor, environmentVariableProvider);

        when(processExecutor.execute(anyString(), anyInt(), Matchers.<String>anyVararg()))
                .thenReturn("output that doesn't begin with sat or unsat");

        z3Client.isSat("Demo program");
    }

}

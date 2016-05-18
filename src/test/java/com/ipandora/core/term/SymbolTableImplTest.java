package com.ipandora.core.term;

import com.ipandora.api.predicate.term.Type;
import org.junit.Test;
import org.mockito.Mockito;

import static org.assertj.core.api.Assertions.assertThat;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

public class SymbolTableImplTest {

    @Test
    public void getTypeOrUnknownShouldReturnUnknownForNonRegisteredVariable() {
        SymbolTableImpl symbolTable = new SymbolTableImpl();
        Type type = symbolTable.getTypeOrUnknown("x");
        assertThat(type).isEqualTo(Type.UNKNOWN);
    }

    @Test
    public void getTypeOrUnknownShouldReturnNatForRegisteredNatVariable() {
        SymbolTableImpl symbolTable = new SymbolTableImpl();
        symbolTable.addMapping("x", Type.NAT);
        Type type = symbolTable.getTypeOrUnknown("x");
        assertThat(type).isEqualTo(Type.NAT);
    }

    @Test
    public void getTypeShouldReturnNullForNonRegisteredVariable() {
        SymbolTableImpl symbolTable = new SymbolTableImpl();
        Type type = symbolTable.getType("x");
        assertThat(type).isNull();
    }

    @Test
    public void getTypeShouldReturnNatForRegisteredNatVariable() {
        SymbolTableImpl symbolTable = new SymbolTableImpl();
        symbolTable.addMapping("x", Type.NAT);
        Type type = symbolTable.getType("x");
        assertThat(type).isEqualTo(Type.NAT);
    }

    @Test
    public void getParentShouldReturnNullIfNoParentSet() {
        SymbolTableImpl symbolTable = new SymbolTableImpl();
        SymbolTable parent = symbolTable.getParent();
        assertThat(parent).isNull();
    }

    @Test
    public void getParentShouldReturnParentIfParentSet() {
        SymbolTableImpl symbolTable = new SymbolTableImpl();
        SymbolTableImpl parent = new SymbolTableImpl();
        symbolTable.setParent(parent);
        SymbolTable returnedParent = symbolTable.getParent();
        assertThat(returnedParent).isEqualTo(returnedParent);
    }

    @Test
    public void getTypeOrUnknownShouldAskParentIfNoMappingFoundInCurrent() {
        SymbolTableImpl symbolTable = new SymbolTableImpl();
        SymbolTable mockParent = Mockito.mock(SymbolTable.class);
        symbolTable.setParent(mockParent);
        symbolTable.getTypeOrUnknown("x");
        verify(mockParent).getType("x");
    }

    @Test
    public void getTypeOrUnknownShouldReturnParentAnswerIfNoMappingFoundInCurrentTable() {
        SymbolTableImpl symbolTable = new SymbolTableImpl();
        SymbolTable mockParent = Mockito.mock(SymbolTable.class);
        when(mockParent.getType("x")).thenReturn(Type.NAT);
        symbolTable.setParent(mockParent);
        Type type = symbolTable.getTypeOrUnknown("x");
        assertThat(type).isEqualTo(Type.NAT);
    }

    @Test
    public void getTypeShouldAskParentIfNpMappingFoundInCurrent() {
        SymbolTableImpl symbolTable = new SymbolTableImpl();
        SymbolTable mockParent = Mockito.mock(SymbolTable.class);
        symbolTable.setParent(mockParent);
        symbolTable.getType("x");
        verify(mockParent).getType("x");
    }

    @Test
    public void getTypeShouldReturnParentAnswerIfNoMappingFoundInCurrentTable() {
        SymbolTableImpl symbolTable = new SymbolTableImpl();
        SymbolTable mockParent = Mockito.mock(SymbolTable.class);
        when(mockParent.getType("x")).thenReturn(Type.NAT);
        symbolTable.setParent(mockParent);
        Type type = symbolTable.getType("x");
        assertThat(type).isEqualTo(Type.NAT);
    }

}
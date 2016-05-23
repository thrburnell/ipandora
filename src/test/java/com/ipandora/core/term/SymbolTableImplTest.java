package com.ipandora.core.term;

import com.ipandora.api.predicate.term.FunctionPrototype;
import com.ipandora.api.predicate.term.Type;
import org.junit.Test;
import org.mockito.Mockito;

import java.util.Collections;

import static org.assertj.core.api.Assertions.assertThat;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

public class SymbolTableImplTest {

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
    public void getFunctionPrototypeShouldReturnNullForNonRegisteredFunctions() {
        SymbolTableImpl symbolTable = new SymbolTableImpl();
        FunctionPrototype prototype = symbolTable.getFunctionPrototype("Foo");
        assertThat(prototype).isNull();
    }

    @Test
    public void getFunctionPrototypeShouldReturnPrototypeForRegisteredFunction() {
        SymbolTableImpl symbolTable = new SymbolTableImpl();
        FunctionPrototype prototype = new FunctionPrototype("Foo", Collections.singletonList(Type.UNKNOWN), Type.NAT);
        symbolTable.addMapping("Foo", prototype);
        assertThat(symbolTable.getFunctionPrototype("Foo")).isEqualTo(prototype);
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
    public void getTypeShouldAskParentIfNoMappingFoundInCurrent() {
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

    @Test
    public void getFunctionPrototypeShouldAskParentIfNoMappingFoundInCurrent() {
        SymbolTableImpl symbolTable = new SymbolTableImpl();
        SymbolTable mockParent = Mockito.mock(SymbolTable.class);
        symbolTable.setParent(mockParent);
        symbolTable.getFunctionPrototype("Foo");
        verify(mockParent).getFunctionPrototype("Foo");
    }

    @Test
    public void getFunctionPrototypeShouldReturnParentAnswerIfNoMappingFoundInCurrentTable() {
        SymbolTableImpl symbolTable = new SymbolTableImpl();
        SymbolTable mockParent = Mockito.mock(SymbolTable.class);
        FunctionPrototype prototype = new FunctionPrototype("Foo", Collections.singletonList(Type.UNKNOWN), Type.NAT);
        when(mockParent.getFunctionPrototype("Foo")).thenReturn(prototype);
        symbolTable.setParent(mockParent);
        assertThat(symbolTable.getFunctionPrototype("Foo")).isEqualTo(prototype);
    }

}
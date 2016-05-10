package com.ipandora.core.term;

import com.ipandora.core.util.Creator;

public class SymbolTableCreator implements Creator<SymbolTable> {

    @Override
    public SymbolTable create() {
        return new SymbolTableImpl();
    }

}

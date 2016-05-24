package com.ipandora.core.function;

import com.ipandora.api.predicate.function.FunctionDefinition;
import com.ipandora.api.predicate.function.FunctionPrototype;
import com.ipandora.api.predicate.term.TypeMismatchException;
import com.ipandora.core.formula.FormulaBuildingVisitor;
import com.ipandora.core.term.SymbolTable;
import com.ipandora.core.term.SymbolTableCreator;
import com.ipandora.core.term.TermBuildingVisitor;
import com.ipandora.core.util.WrappingRuntimeException;
import com.ipandora.parser.PredicateLogicLexer;
import com.ipandora.parser.PredicateLogicParser;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.BailErrorStrategy;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.misc.ParseCancellationException;

import java.util.Collections;
import java.util.List;

public class ANTLRFunctionParser implements FunctionParser {

    private final FunctionTypeChecker functionTypeChecker;

    public ANTLRFunctionParser(FunctionTypeChecker functionTypeChecker) {
        this.functionTypeChecker = functionTypeChecker;
    }

    @Override
    public FunctionDefinition fromString(String function) throws FunctionParsingException {
        return fromString(function, Collections.<FunctionPrototype>emptyList());
    }

    @Override
    public FunctionDefinition fromString(String function, List<FunctionPrototype> functionPrototypes)
            throws FunctionParsingException {

        ANTLRInputStream stream = new ANTLRInputStream(function);
        PredicateLogicLexer lexer = new PredicateLogicLexer(stream);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        PredicateLogicParser parser = new PredicateLogicParser(tokens);
        parser.setErrorHandler(new BailErrorStrategy());

        PredicateLogicParser.FunctionDefinitionContext fnCtx;

        try {
            fnCtx = parser.functionDefinition();
        } catch (ParseCancellationException e) {
            throw new FunctionParsingException("Invalid function: " + function);
        }

        SymbolTableCreator stCreator = new SymbolTableCreator();
        SymbolTable rootSymbolTable = populateSymbolTable(stCreator.create(), functionPrototypes);
        FunctionBuildingVisitor functionBuildingVisitor = makeFunctionBuildingVisitor(rootSymbolTable, stCreator);

        try {
            return functionBuildingVisitor.visit(fnCtx);
        } catch (IllegalFunctionException e) {
            throw new FunctionParsingException(e);
        } catch (WrappingRuntimeException e) {
            throw new FunctionParsingException(e.getWrappedException());
        }
    }

    @Override
    public FunctionDefinition fromStringWithTypeChecking(String function) throws FunctionParsingException {
        return fromStringWithTypeChecking(function, Collections.<FunctionPrototype>emptyList());
    }

    @Override
    public FunctionDefinition fromStringWithTypeChecking(String function, List<FunctionPrototype> functionPrototypes)
            throws FunctionParsingException {

        FunctionDefinition f = fromString(function, functionPrototypes);

        try {
            functionTypeChecker.analyse(f);
        } catch (TypeMismatchException e) {
            throw new FunctionParsingException(e);
        }

        return f;
    }

    private FunctionBuildingVisitor makeFunctionBuildingVisitor(SymbolTable rootSymbolTable,
                                                                SymbolTableCreator symbolTableCreator) {

        TermBuildingVisitor termVisitor = new TermBuildingVisitor(rootSymbolTable, symbolTableCreator);
        FormulaBuildingVisitor formulaVisitor = new FormulaBuildingVisitor(termVisitor);
        return new FunctionBuildingVisitor(formulaVisitor, termVisitor);
    }

    private SymbolTable populateSymbolTable(SymbolTable symbolTable, List<FunctionPrototype> functionPrototypes) {
        for (FunctionPrototype prototype : functionPrototypes) {
            symbolTable.addMapping(prototype.getName(), prototype);
        }
        return symbolTable;
    }

}

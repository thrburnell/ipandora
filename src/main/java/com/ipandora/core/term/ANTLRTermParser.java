package com.ipandora.core.term;

import com.ipandora.api.predicate.function.FunctionPrototype;
import com.ipandora.api.predicate.term.Term;
import com.ipandora.api.predicate.term.TypeMismatchException;
import com.ipandora.core.util.WrappingRuntimeException;
import com.ipandora.parser.PredicateLogicLexer;
import com.ipandora.parser.PredicateLogicParser;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.BailErrorStrategy;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.misc.ParseCancellationException;

import java.util.Collections;
import java.util.List;

public class ANTLRTermParser implements TermParser {

    private final TermTypeChecker termTypeChecker;

    public ANTLRTermParser(TermTypeChecker termTypeChecker) {
        this.termTypeChecker = termTypeChecker;
    }

    @Override
    public Term fromString(String term) throws TermParsingException {
        return fromString(term, Collections.<FunctionPrototype>emptyList());
    }

    @Override
    public Term fromString(String term, List<FunctionPrototype> functionPrototypes) throws TermParsingException {
        ANTLRInputStream stream = new ANTLRInputStream(term);
        PredicateLogicLexer lexer = new PredicateLogicLexer(stream);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        PredicateLogicParser parser = new PredicateLogicParser(tokens);
        parser.setErrorHandler(new BailErrorStrategy());

        SymbolTableCreator stCreator = new SymbolTableCreator();
        SymbolTable rootSymbolTable = populateSymbolTable(stCreator.create(), functionPrototypes);
        TermBuildingVisitor termBuildingVisitor = makeTermBuildingVisitor(rootSymbolTable, stCreator);

        try {
            return termBuildingVisitor.visit(parser.mathExprOnly());
        } catch (ParseCancellationException e) {
            throw new TermParsingException("Invalid term: " + term);
        } catch (WrappingRuntimeException e) {
            throw new TermParsingException(e.getWrappedException());
        }
    }

    @Override
    public Term fromStringWithTypeChecking(String term) throws TermParsingException {
        return fromStringWithTypeChecking(term, Collections.<FunctionPrototype>emptyList());
    }

    @Override
    public Term fromStringWithTypeChecking(String term, List<FunctionPrototype> functionPrototypes)
            throws TermParsingException {

        try {
            Term t = fromString(term, functionPrototypes);
            termTypeChecker.analyse(t);
            return t;
        } catch (TypeMismatchException e) {
            throw new TermParsingException(e);
        }
    }

    private TermBuildingVisitor makeTermBuildingVisitor(SymbolTable rootSymbolTable,
                                                        SymbolTableCreator symbolTableCreator) {
        return new TermBuildingVisitor(rootSymbolTable, symbolTableCreator);
    }

    private SymbolTable populateSymbolTable(SymbolTable symbolTable, List<FunctionPrototype> functionPrototypes) {
        for (FunctionPrototype prototype : functionPrototypes) {
            symbolTable.addMapping(prototype.getName(), prototype);
        }
        return symbolTable;
    }

}

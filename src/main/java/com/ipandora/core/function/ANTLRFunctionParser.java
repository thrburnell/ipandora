package com.ipandora.core.function;

import com.ipandora.api.predicate.function.Function;
import com.ipandora.api.predicate.term.TypeMismatchException;
import com.ipandora.core.formula.FormulaBuildingVisitor;
import com.ipandora.core.term.SymbolTableCreator;
import com.ipandora.core.term.TermBuildingVisitor;
import com.ipandora.parser.PredicateLogicLexer;
import com.ipandora.parser.PredicateLogicParser;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;

public class ANTLRFunctionParser implements FunctionParser {

    @Override
    public Function fromString(String function) throws FunctionParsingException {
        // TODO: fail on any parsing error
        ANTLRInputStream stream = new ANTLRInputStream(function);
        PredicateLogicLexer lexer = new PredicateLogicLexer(stream);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        PredicateLogicParser parser = new PredicateLogicParser(tokens);
        PredicateLogicParser.FunctionDefinitionContext fnCtx = parser.functionDefinition();
        SymbolTableCreator symbolTableCreator = new SymbolTableCreator();


        // TEMP: Func and Form visitors need same Term visitor for symbol table reasons
        // This won't be necessary once semantic analysis is abstracted and not performed at parse time
        TermBuildingVisitor termVisitor = new TermBuildingVisitor(symbolTableCreator);
        FormulaBuildingVisitor formulaVisitor = new FormulaBuildingVisitor(termVisitor);

        FunctionBuildingVisitor visitor = new FunctionBuildingVisitor(formulaVisitor, termVisitor);

        try {
            return visitor.visit(fnCtx);
        } catch (TypeMismatchException | IllegalFunctionException e) {
            throw new FunctionParsingException(e);
        }
    }

}

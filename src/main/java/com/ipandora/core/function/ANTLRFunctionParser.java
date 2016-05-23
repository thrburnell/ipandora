package com.ipandora.core.function;

import com.ipandora.api.predicate.function.Function;
import com.ipandora.core.formula.FormulaBuildingVisitor;
import com.ipandora.core.term.SymbolTableCreator;
import com.ipandora.core.term.TermBuildingVisitor;
import com.ipandora.core.util.WrappingRuntimeException;
import com.ipandora.parser.PredicateLogicLexer;
import com.ipandora.parser.PredicateLogicParser;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.BailErrorStrategy;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.misc.ParseCancellationException;

public class ANTLRFunctionParser implements FunctionParser {

    @Override
    public Function fromString(String function) throws FunctionParsingException {
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

        try {
            return makeFunctionBuildingVisitor().visit(fnCtx);
        } catch (IllegalFunctionException e) {
            throw new FunctionParsingException(e);
        } catch (WrappingRuntimeException e) {
            throw new FunctionParsingException(e.getWrappedException());
        }
    }

    private FunctionBuildingVisitor makeFunctionBuildingVisitor() {
        SymbolTableCreator symbolTableCreator = new SymbolTableCreator();
        TermBuildingVisitor termVisitor = new TermBuildingVisitor(symbolTableCreator.create(), symbolTableCreator);
        FormulaBuildingVisitor formulaVisitor = new FormulaBuildingVisitor(termVisitor);

        return new FunctionBuildingVisitor(formulaVisitor, termVisitor);
    }

}

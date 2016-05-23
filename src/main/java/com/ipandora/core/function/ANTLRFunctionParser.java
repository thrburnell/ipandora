package com.ipandora.core.function;

import com.ipandora.api.predicate.function.Function;
import com.ipandora.core.formula.FormulaBuildingVisitor;
import com.ipandora.core.term.SymbolTableCreator;
import com.ipandora.core.term.TermBuildingVisitor;
import com.ipandora.core.util.WrappingRuntimeException;
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

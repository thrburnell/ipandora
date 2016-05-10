package com.ipandora.core.formula;

import com.ipandora.api.predicate.formula.Formula;
import com.ipandora.api.predicate.term.TypeMismatchException;
import com.ipandora.core.term.SymbolTableCreator;
import com.ipandora.core.term.TermBuildingVisitor;
import com.ipandora.parser.PredicateLogicLexer;
import com.ipandora.parser.PredicateLogicParser;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;

public class ANTLRFormulaParser implements FormulaParser {

    public Formula fromString(String formula) throws FormulaParsingException {
        // TODO: fail on any parsing error
        ANTLRInputStream stream = new ANTLRInputStream(formula);
        PredicateLogicLexer lexer = new PredicateLogicLexer(stream);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        PredicateLogicParser parser = new PredicateLogicParser(tokens);
        PredicateLogicParser.FormulaContext formulaCtx = parser.formula();
        SymbolTableCreator symbolTableCreator = new SymbolTableCreator();
        FormulaBuildingVisitor visitor = new FormulaBuildingVisitor(new TermBuildingVisitor(symbolTableCreator));

        try {
            return visitor.visit(formulaCtx);
        } catch (TypeMismatchException | IllegalFormulaException e) {
            throw new FormulaParsingException(e);
        }
    }

}

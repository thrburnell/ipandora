package com.ipandora.core.formula;

import com.ipandora.api.predicate.formula.Formula;
import com.ipandora.api.predicate.term.TypeMismatchException;
import com.ipandora.core.term.SymbolTableCreator;
import com.ipandora.core.term.TermBuildingVisitor;
import com.ipandora.core.util.WrappingRuntimeException;
import com.ipandora.parser.PredicateLogicLexer;
import com.ipandora.parser.PredicateLogicParser;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.BailErrorStrategy;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.misc.ParseCancellationException;

public class ANTLRFormulaParser implements FormulaParser {

    private final FormulaTypeChecker formulaTypeChecker;

    public ANTLRFormulaParser(FormulaTypeChecker formulaTypeChecker) {
        this.formulaTypeChecker = formulaTypeChecker;
    }

    @Override
    public Formula fromStringWithTypeChecking(String formula) throws FormulaParsingException {

        Formula form = fromString(formula);
        try {
            formulaTypeChecker.analyse(form);
        } catch (TypeMismatchException e) {
            throw new FormulaParsingException(e);
        }
        return form;
    }

    @Override
    public Formula fromString(String formula) throws FormulaParsingException {
        ANTLRInputStream stream = new ANTLRInputStream(formula);
        PredicateLogicLexer lexer = new PredicateLogicLexer(stream);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        PredicateLogicParser parser = new PredicateLogicParser(tokens);
        parser.setErrorHandler(new BailErrorStrategy());

        PredicateLogicParser.FormulaContext formulaCtx;
        try {
            formulaCtx = parser.formula();
        } catch (ParseCancellationException e) {
            throw new FormulaParsingException("Invalid formula: " + formula);
        }

        try {
            return makeFormulaBuildingVisitor().visit(formulaCtx);
        } catch (WrappingRuntimeException e) {
            throw new FormulaParsingException(e.getWrappedException());
        }
    }

    private FormulaBuildingVisitor makeFormulaBuildingVisitor() {
        SymbolTableCreator stCreator = new SymbolTableCreator();
        TermBuildingVisitor termBuildingVisitor = new TermBuildingVisitor(stCreator.create(), stCreator);
        return new FormulaBuildingVisitor(termBuildingVisitor);
    }

}

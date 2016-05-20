package com.ipandora.core.formula;

import com.ipandora.api.predicate.formula.Formula;
import com.ipandora.core.util.WrappingRuntimeException;
import com.ipandora.parser.PredicateLogicLexer;
import com.ipandora.parser.PredicateLogicParser;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.BailErrorStrategy;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.misc.ParseCancellationException;

public class ANTLRFormulaParser implements FormulaParser {

    private final FormulaBuildingVisitor formulaBuildingVisitor;
    private final FormulaTypeChecker formulaTypeChecker;

    public ANTLRFormulaParser(FormulaBuildingVisitor formulaBuildingVisitor, FormulaTypeChecker formulaTypeChecker) {
        this.formulaBuildingVisitor = formulaBuildingVisitor;
        this.formulaTypeChecker = formulaTypeChecker;
    }

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
            Formula form = formulaBuildingVisitor.visit(formulaCtx);
            formulaTypeChecker.analyse(form);
            return form;
        } catch (WrappingRuntimeException e) {
            throw new FormulaParsingException(e.getWrappedException());
        }
    }

}

package com.ipandora.core.formula;

import com.ipandora.api.predicate.formula.Formula;
import com.ipandora.core.util.WrappingRuntimeException;
import com.ipandora.parser.PredicateLogicLexer;
import com.ipandora.parser.PredicateLogicParser;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;

public class ANTLRFormulaParser implements FormulaParser {

    private final FormulaBuildingVisitor formulaBuildingVisitor;
    private final TypeCheckAnalyser typeCheckAnalyser;

    public ANTLRFormulaParser(FormulaBuildingVisitor formulaBuildingVisitor, TypeCheckAnalyser typeCheckAnalyser) {
        this.formulaBuildingVisitor = formulaBuildingVisitor;
        this.typeCheckAnalyser = typeCheckAnalyser;
    }

    public Formula fromString(String formula) throws FormulaParsingException {
        // TODO: fail on any parsing error
        ANTLRInputStream stream = new ANTLRInputStream(formula);
        PredicateLogicLexer lexer = new PredicateLogicLexer(stream);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        PredicateLogicParser parser = new PredicateLogicParser(tokens);
        PredicateLogicParser.FormulaContext formulaCtx = parser.formula();

        try {
            Formula form = formulaBuildingVisitor.visit(formulaCtx);
            typeCheckAnalyser.analyse(form);
            return form;
        } catch (IllegalFormulaException e) {
            throw new FormulaParsingException(e);
        } catch (WrappingRuntimeException e) {
            throw new FormulaParsingException(e.getWrappedException());
        }
    }

}

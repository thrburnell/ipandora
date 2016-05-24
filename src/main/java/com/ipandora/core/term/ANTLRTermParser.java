package com.ipandora.core.term;

import com.ipandora.api.predicate.term.Term;
import com.ipandora.api.predicate.term.TypeMismatchException;
import com.ipandora.core.util.WrappingRuntimeException;
import com.ipandora.parser.PredicateLogicLexer;
import com.ipandora.parser.PredicateLogicParser;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.BailErrorStrategy;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.misc.ParseCancellationException;

public class ANTLRTermParser implements TermParser {

    private final TermBuildingVisitor termBuildingVisitor;
    private final TermTypeChecker termTypeChecker;

    public ANTLRTermParser(TermBuildingVisitor termBuildingVisitor, TermTypeChecker termTypeChecker) {
        this.termBuildingVisitor = termBuildingVisitor;
        this.termTypeChecker = termTypeChecker;
    }

    @Override
    public Term fromString(String term) throws TermParsingException {
        ANTLRInputStream stream = new ANTLRInputStream(term);
        PredicateLogicLexer lexer = new PredicateLogicLexer(stream);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        PredicateLogicParser parser = new PredicateLogicParser(tokens);
        parser.setErrorHandler(new BailErrorStrategy());

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
        try {
            Term t = fromString(term);
            termTypeChecker.analyse(t);
            return t;
        } catch (TypeMismatchException e) {
            throw new TermParsingException(e);
        }
    }

}

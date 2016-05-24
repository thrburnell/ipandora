package com.ipandora.core.term;

import com.ipandora.api.predicate.function.FunctionPrototype;
import com.ipandora.api.predicate.term.Term;

import java.util.List;

public interface TermParser {

    Term fromString(String term) throws TermParsingException;
    Term fromString(String term, List<FunctionPrototype> functionPrototypes) throws TermParsingException;

    Term fromStringWithTypeChecking(String term) throws TermParsingException;
    Term fromStringWithTypeChecking(String term, List<FunctionPrototype> functionPrototypes)
            throws TermParsingException;

}

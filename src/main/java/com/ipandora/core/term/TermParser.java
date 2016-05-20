package com.ipandora.core.term;

import com.ipandora.api.predicate.term.Term;

public interface TermParser {

    Term fromString(String term) throws TermParsingException;

}

package com.ipandora.api.predicate.term;

import com.ipandora.core.term.TermVisitor;

public interface Term {

    <T> T accept(TermVisitor<T> visitor);

}

package com.ipandora.core.formula;

import com.ipandora.api.predicate.formula.Formula;

import java.util.List;

public interface FormulaSplitter<T> {

    List<Formula> split(T formula);

}

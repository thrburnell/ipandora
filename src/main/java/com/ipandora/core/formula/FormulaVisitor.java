package com.ipandora.core.formula;

import com.ipandora.api.predicate.formula.*;

public interface FormulaVisitor<T> {

    T visitAtomFormula(AtomFormula atomFormula);

    T visitAndFormula(AndFormula andFormula);
    T visitOrFormula(OrFormula orFormula);

    T visitForallFormula(ForallFormula forallFormula);
    T visitExistsFormula(ExistsFormula existsFormula);

    T visitTrueFormula(TrueFormula trueFormula);
    T visitFalseFormula(FalseFormula falseFormula);

    T visitIffFormula(IffFormula iffFormula);
    T visitImpliesFormula(ImpliesFormula impliesFormula);

    T visitNotFormula(NotFormula notFormula);

    T visitPredicateFormula(PredicateFormula predicateFormula);

}

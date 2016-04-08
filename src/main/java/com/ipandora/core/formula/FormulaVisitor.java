package com.ipandora.core.formula;

import com.ipandora.api.predicate.formula.*;

public interface FormulaVisitor<T> {

    T visit(Formula formula);

    T visitAndFormula(AndFormula andFormula);
    T visitOrFormula(OrFormula orFormula);

    T visitForallFormula(ForallFormula forallFormula);
    T visitExistsFormula(ExistsFormula existsFormula);

    T visitTrueFormula(TrueFormula trueFormula);
    T visitFalseFormula(FalseFormula falseFormula);

    T visitImpliesFormula(ImpliesFormula impliesFormula);
    T visitIffFormula(IffFormula iffFormula);

    T visitNotFormula(NotFormula notFormula);

    T visitPredicateFormula(PredicateFormula predicateFormula);

}

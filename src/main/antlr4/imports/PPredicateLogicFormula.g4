parser grammar PPredicateLogicFormula;
import PShared, PPredicateLogicTerm;

// Formulas

entireFormula
    : form=formula EOF
    ;

formula
    : lhs=iffElement (IFF rhs=formula)?
    ;

iffElement
    : lhs=impliesElement (IMPLIES rhs=iffElement)?;

impliesElement
    : lhs=conjunction (OR rhs=impliesElement)?;

conjunction
    : lhs=negElement (AND rhs=conjunction)?;

negElement
    : (not=NOT)? elem=element;

element
    : quant=quantified
    | pred=predicate
    | expr=boolExpr
    | tf=(TRUTH | FALSITY)
    | LPAREN form=formula RPAREN
    ;

quantified
    : quant=(FORALL | EXISTS) varSets+=varSet (COMMA varSets+=varSet)* DOT elem=negElement
    ;

varSet
    : vars+=anyName (COMMA vars+=anyName)* (dom=domain)?
    ;

domain
    : IN type=CAP_NAME_ONLY_LETTERS
    ;

// Optional argList; when missing, predicate is a propositional variable
predicate
    : name=anyName args=argList?
    ;

boolExpr
    : lhs=mathExpr op=(ET | GT | LT | GTE | LTE) rhs=mathExpr
    ;


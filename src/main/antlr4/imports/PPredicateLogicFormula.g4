parser grammar PPredicateLogicFormula;
import PPredicateLogicTerm;

// Mathematical functions

// TODO: separate functions out into separate grammar
functionDefinition
    : name=NAME args=fnArgList ET (cases+=fnCase)+
    ;

fnArgList
    : LPAREN (args+=NAME (COMMA args+=NAME)*)? RPAREN
    ;

fnCase
    : expr=mathExpr IF cond=formula
    | expr=mathExpr OTHERWISE?
    ;

// Formulas

formula
    : lhs=iffElement (IFF rhs=formula)?;

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
    : vars+=NAME (COMMA vars+=NAME)* (dom=domain)?
    ;

domain
    : IN type=NAT
    ;

// Optional argList; when missing, predicate is a propositional variable
predicate
    : name=NAME args=argList?
    ;

boolExpr
    : lhs=mathExpr op=(ET | GT | LT | GTE | LTE) rhs=mathExpr
    ;


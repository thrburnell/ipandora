grammar PredicateLogic;

@header {
package com.ipandora.parser;
}

// Mathematical functions

functionDefinition
    : name=NAME args=fnArgList ET (cases+=fnCase)+
    ;

fnArgList
    : LPAREN (args+=NAME (',' args+=NAME)*)? RPAREN
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
    : quant=(FORALL | EXISTS) varSets+=varSet (',' varSets+=varSet)* '.' elem=negElement
    ;

varSet
    : vars+=NAME (',' vars+=NAME)* (dom=domain)?
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

argList
    : LPAREN args+=mathExpr (',' args+=mathExpr)* RPAREN
    ;


// Terms

mathExpr
    : lhs=mathExpr op=(PLUS | MINUS) rhs=mathTerm
    | term=sumExpr
    ;

sumExpr
    : SUM var=NAME lower=mathExpr upper=mathExpr elem=sumExpr
    | term=mathTerm
    ;

mathTerm
    : lhs=mathTerm op=(MULTIPLY | DIVIDE) rhs=powerTerm
    | term=powerTerm
    ;

powerTerm
    : base=powerTerm POWER exponent=NUMBER
    | term=leafTerm
    ;

leafTerm
    : func=function
    | term=NAME
    | number=NUMBER
    | LPAREN expr=mathExpr RPAREN
    ;

function
    : name=NAME args=argList
    ;

// Connectives
NOT: '!';
AND: '&';
OR : '|';
IFF: '<->';
IMPLIES: '->';
LPAREN: '(';
RPAREN: ')';
FORALL: '\\FORALL';
EXISTS: '\\EXISTS';
TRUTH: '\\TRUTH';
FALSITY: '\\FALSITY';

// Mathematical expressions
PLUS: '+';
MINUS: '-';
MULTIPLY: '*';
DIVIDE: '/';
POWER: '^';
SUM: '\\SUM';

// Boolean operators
ET: '=';
GT: '>';
LT: '<';
GTE: '>=';
LTE: '<=';

// Types
IN: 'in';
NAT: 'Nat';

// Function definitions
IF: 'if';
OTHERWISE: 'otherwise';

// These need to be at the end so string literals above take precedence
NAME: LETTER CHARACTER*;
NUMBER: DIGIT+;
fragment CHARACTER: LETTER | DIGIT | '_';
fragment LETTER: ('a'..'z' | 'A'..'Z');
fragment DIGIT: ('0'..'9');

WS: (' ' | '\t' | '\r' | '\n')+ -> skip;

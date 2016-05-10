grammar PredicateLogic;

@header {
package com.ipandora.parser;
}

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
    | LPAREN form=formula RPAREN
    ;

quantified
    : quant=(FORALL | EXISTS) var=VARIABLE elem=negElement
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

mathExpr
    : lhs=mathExpr op=(PLUS | MINUS) rhs=mathTerm
    | term=sumExpr
    ;

sumExpr
    : SUM var=VARIABLE lower=mathExpr upper=mathExpr elem=sumExpr
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
    | var=VARIABLE
    | constant=NAME
    | number=NUMBER
    | LPAREN expr=mathExpr RPAREN
    ;

function
    : name=NAME args=argList
    ;


VARIABLE: '?' ('a'..'z') CHARACTER*;
NAME: LETTER CHARACTER*;
NUMBER: DIGIT+;
fragment CHARACTER: LETTER | DIGIT | '_';
fragment LETTER: ('a'..'z' | 'A'..'Z');
fragment DIGIT: ('0'..'9');

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

WS: (' ' | '\t' | '\r' | '\n')+ -> skip;

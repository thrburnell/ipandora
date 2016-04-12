grammar PredicateLogic;

@header {
package com.ipandora.parser;
}

formula
    : lhs=iffElement (IFF rhs=iffElement)?;

iffElement
    : lhs=impliesElement (IMPLIES rhs=impliesElement)?;

impliesElement
    : lhs=conjunction (OR rhs=conjunction)?;

conjunction
    : lhs=negElement (AND rhs=negElement)?;

negElement
    : (not=NOT)? elem=element;

element
    : quant=quantified
    | pred=predicate
    | LPAREN form=formula RPAREN
    ;

quantified
    : quant=(FORALL | EXISTS) var=VARIABLE elem=negElement
    ;

predicate
    : name=PREDICATE LPAREN args=argList RPAREN
    ;

argList
    : args+=arg (',' args+=arg)*
    ;

arg
    : var=VARIABLE
    ;

VARIABLE: '?' ('a'..'z') CHARACTER*;
PREDICATE: ('A'..'Z') CHARACTER*;
fragment CHARACTER: LETTER | DIGIT | '_';
fragment LETTER: ('a'..'z' | 'A'..'Z');
fragment DIGIT: ('0'..'9');

NOT: '!';
AND: '&';
OR : '|';
IFF: '<->';
IMPLIES: '->';
LPAREN: '(';
RPAREN: ')';
FORALL: '\\FORALL';
EXISTS: '\\EXISTS';
WS: (' ' | '\t' | '\r' | '\n')+ -> skip;

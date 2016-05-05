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
    | LPAREN form=formula RPAREN
    ;

quantified
    : quant=(FORALL | EXISTS) var=VARIABLE elem=negElement
    ;

// Optional argList; when missing, predicate is a propositional variable
predicate
    : name=PREDICATE args=argList?
    ;

argList
    : LPAREN args+=arg (',' args+=arg)* RPAREN
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

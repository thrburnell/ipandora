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
    : LPAREN args+=mathExpr (',' args+=mathExpr)* RPAREN
    ;

mathExpr
    : lhs=mathExpr op=(PLUS | MINUS) rhs=mathTerm
    | term=mathTerm
    ;

mathTerm
    : lhs=mathTerm op=(MULTIPLY | DIVIDE) rhs=leafTerm
    | term=leafTerm
    ;

leafTerm
    : var=VARIABLE
    | constant=CONSTANT
    | LPAREN expr=mathExpr RPAREN
    ; // TODO add support for number


VARIABLE: '?' ('a'..'z') CHARACTER*;
CONSTANT: ('a'..'z') CHARACTER*;
PREDICATE: ('A'..'Z') CHARACTER*;
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

WS: (' ' | '\t' | '\r' | '\n')+ -> skip;

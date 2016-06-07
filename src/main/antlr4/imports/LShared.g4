lexer grammar LShared;

// IMPORTANT: This grammar needs to be imported last so string literals in other
// lexer grammars take precedence

DOT: '.';
COMMA: ',';
CAP_NAME_ONLY_LETTERS: ('A'..'Z') LETTER*;
NAME: LETTER CHARACTER*;
NUMBER: DIGIT+;
fragment CHARACTER: LETTER | DIGIT | '_';
fragment LETTER: ('a'..'z' | 'A'..'Z');
fragment DIGIT: ('0'..'9');

WS: (' ' | '\t' | '\r' | '\n')+ -> skip;
LINE_COMMENT: '//' ~[\r\n]* -> skip;
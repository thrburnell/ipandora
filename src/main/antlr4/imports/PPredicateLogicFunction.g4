parser grammar PPredicateLogicFunction;
import PPredicateLogicFormula, PPredicateLogicTerm;

functionDefinition
    : name=(NAME | CAP_NAME_ONLY_LETTERS) args=fnArgList ET cases=fnCases
    ;

fnArgList
    : LPAREN (args+=(NAME | CAP_NAME_ONLY_LETTERS) (COMMA args+=(NAME | CAP_NAME_ONLY_LETTERS))*)? RPAREN
    ;

fnCases
    : ifFnCase=ifCase rest=fnCases
    | otherwiseFnCase=otherwiseCase
    ;

ifCase
    : expr=mathExpr IF cond=formula
    ;

otherwiseCase
    : expr=mathExpr OTHERWISE?
    ;

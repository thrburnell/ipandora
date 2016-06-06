parser grammar PPredicateLogicFunction;
import PPredicateLogicFormula, PPredicateLogicTerm;

functionDefinition
    : name=NAME args=fnArgList ET cases=fnCases
    ;

fnArgList
    : LPAREN (args+=NAME (COMMA args+=NAME)*)? RPAREN
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

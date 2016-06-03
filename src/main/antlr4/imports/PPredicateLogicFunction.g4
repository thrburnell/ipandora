parser grammar PPredicateLogicFunction;
import PPredicateLogicFormula, PPredicateLogicTerm;

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
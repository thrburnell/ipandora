parser grammar PPredicateLogicFunction;
import PShared, PPredicateLogicFormula, PPredicateLogicTerm;

// Sum :: Nat -> Nat

functionDefinition
    : proto=functionPrototype def=definition
    ;

// Prototype
functionPrototype
    : name=anyName DOUBLE_COLON types=protoTypeList
    ;

protoTypeList
    : types+=CAP_NAME_ONLY_LETTERS (IMPLIES types+=CAP_NAME_ONLY_LETTERS)*
    ;

protoReturnType
    : type=CAP_NAME_ONLY_LETTERS
    ;

// Definition
definition
    : name=anyName args=fnArgList ET cases=fnCases
    ;

fnArgList
    : LPAREN (args+=anyName (COMMA args+=anyName)*)? RPAREN
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

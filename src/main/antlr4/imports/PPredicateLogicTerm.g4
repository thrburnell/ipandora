parser grammar PPredicateLogicTerm;

argList
    : LPAREN args+=mathExpr (COMMA args+=mathExpr)* RPAREN
    ;

// Terms

// Top-level term rule for use in term-only parsing
// When using a PredicateLogic parser, call parser.mathExprOnly() to match on only a mathExpr (i.e. failing to parse
// if mathExpr used in, for example, a boolean expression (mathExpr >= mathExpr))
mathExprOnly
    : expr=mathExpr EOF
    ;

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
grammar LogicFormula;

// Regole per generare le espressioni logiche
formula : expression EOF ;

expression
    : NOT expression                     #notExpr
    | expression AND expression          #andExpr
    | expression OR expression           #orExpr
    | expression IMPLIES expression      #impliesExpr
    | expression IFF expression          #iffExpr
    | LPAREN expression RPAREN           #parenExpr
    | IDENTIFIER                         #variableExpr
    | TRUE                               #trueExpr
    | FALSE                              #falseExpr
    ;


// Regole del lexer
TRUE  : 'top' | 'TOP';
FALSE : 'bottom' | 'BOTTOM';

NOT     : '!' | 'not' | 'NOT';
AND     : '&' | 'and' | 'AND';
OR      : '|' | 'or' | 'OR';
IMPLIES : '->' | '=>' | 'implies' | 'IMPLIES';
IFF     : '<->' | '<=>' | 'iff' | 'IFF';

LPAREN : '(' ;
RPAREN : ')' ;

IDENTIFIER : [a-zA-Z][a-zA-Z0-9_]* ;

// Non fare niente per i whitespace
WHITESPACE : [ \t\r\n]+ -> skip ;
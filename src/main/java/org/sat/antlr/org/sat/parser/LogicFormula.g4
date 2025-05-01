grammar LogicFormula;

/*
 * Grammatica per formule logiche con precedenza degli operatori:
 * Livello 5 (minore): doppia implicazione (<->)
 * Livello 4: implicazione (->)
 * Livello 3: disgiunzione (|)
 * Livello 2: congiunzione (&)
 * Livello 1: negazione (!)
 * Livello 0 (maggiore): atomi, parentesi
 */

// Punto di ingresso della grammatica
formula : biconditional EOF ;

// Livello 5: doppia implicazione (associatività a sinistra)
biconditional
    : implication (IFF implication)*                    #iff
    ;

// Livello 4: implicazione (associatività a destra)
implication
    : disjunction (IMPLIES implication)?                #implies
    ;

// Livello 3: disgiunzione (associatività a sinistra)
disjunction
    : conjunction (OR conjunction)*                     #or
    ;

// Livello 2: congiunzione (associatività a sinistra)
conjunction
    : negation (AND negation)*                          #and
    ;

// Livello 1: negazione
negation
    : NOT negation                                      #not
    | atom                                              #var
    ;

// Livello 0: espressioni atomiche
atom
    : LPAR biconditional RPAR                           #par
    | IDENTIFIER                                        #id
    | TRUE                                              #true
    | FALSE                                             #false
    ;



// Operatori logici
NOT         : '!' | 'not' | 'NOT' ;
AND         : '&' | 'and' | 'AND' ;
OR          : '|' | 'or' | 'OR' ;
IMPLIES     : '->' | '=>' | 'implies' | 'IMPLIES' ;
IFF         : '<->' | '<=>' | 'iff' | 'IFF' ;

// Simboli e identificatori
LPAR        : '(' ;
RPAR        : ')' ;
TRUE        : 'top' | 'TOP' ;
FALSE       : 'bottom' | 'BOTTOM' ;
IDENTIFIER  : [a-zA-Z][a-zA-Z0-9_]* ;

// Ignora whitespace
WHITESPACE  : [ \t\r\n]+ -> skip ;

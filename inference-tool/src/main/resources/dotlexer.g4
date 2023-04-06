lexer grammar dotlexer;

LABEL: [A-z];
ARITY: NUMBER;
NUMBER: ('0' .. '9');
BOOL: 'True' | 'False';

COLON: ':';

STR: '"' ()* '"';
INT: '-'? NUMBER+;
REAL: NUMBER+ '.' NUMBER+;
VALUE:  STR | INT | NUMBER;
VALUELIST: '[' ((VALUE)',')* ']';

VNAME: 'i<sub>' INT '</sub>' | 'r<sub>' INT '</sub>';

AOP: '+' | '-' | '&times;' | '&divide;';
GOP: '=' | '>';
OR: '&or;';
IN: '&isin;';
NOT: '!';
OPEN: '(';
CLOSE: ')';
LANGLE: '[';
RANGLE: ']';
COMMA: ',';
SLASH: '/';
IS: ':=';



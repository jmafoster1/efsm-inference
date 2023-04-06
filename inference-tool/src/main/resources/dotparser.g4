parser grammar dotparser;

options { tokenvocab=arithmeticlexer; }

aexp: VALUE | VNAME | aexp AOP aexp;


gexp: BOOL | aexp GOP aexp | (VNAME IN VALUELIST) | (NOT OPEN gexp OR gexp CLOSE);
guards: LANGLE ((gexp)COMMA)* RANGLE;

outputs: LANGLE ((aexp)COMMA)* RANGLE;
update: VNAME IS aexp;
updates: LANGLE ((update)COMMA)* RANGLE;
rightpart: (SLASH outputs? updates?)?;


transition: LABEL COLON ARITY guards rightpart;
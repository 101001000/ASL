%{
open Ast
let str = Camlcoq.coqstring_of_camlstring
let coq_Z_of_int = Camlcoq.Z.of_sint
%}

%token <int> LIT
%token <string> ID
%token EQUALS
%token SEMICOLON
%token SKIP
%token EOF

%start <Ast.stmt> prog

%%

prog:
	| s = stmt; EOF { s }
	;
	
stmt:
	| x = ID; EQUALS; e = expr {Assign ((str x), e)}
	| s1 = stmt; SEMICOLON; s2 = stmt; {Seq (s1, s2)}
	| SKIP; {Skip}
	;
	
expr:
	| i = LIT { Lit (coq_Z_of_int i) }
	| x = ID { Var (str x) }
	;
	

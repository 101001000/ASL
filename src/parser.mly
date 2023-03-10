%{
open Ast
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
	| x = ID; EQUALS; e = expr {Assign (x, e)}
	| s1 = stmt; SEMICOLON; s2 = stmt; {Seq (s1, s2)}
	| SKIP; {Skip}
	;
	
expr:
	| i = LIT { Lit i }
	| x = ID { Var x }
	;
	

%{ 
	open AST
%}


%token <Camlcoq.Z.t> INT
%token <string> ID
%token SEMI
%token VAR
%token EQ
%token EOF
%token SKIP

%start <AST.prog> main

%%

main:
| ds = decs ss = stmts EOF { Prog (ds,ss) }

stmts:
| s = stmt SEMI {[s]}
| s = stmt SEMI t = stmts {s :: t}

stmt:
| a = assign { a }
| sk = skip { sk }

decs:
| d = dec SEMI {[d]}
| d = dec SEMI t = decs {d :: t}

dec:
| VAR x = ID {Camlcoq.coqstring_of_camlstring x}

expr:
| i = INT { i }

assign:
| i = ID EQ e = expr { Assign(Camlcoq.coqstring_of_camlstring i, e) }

skip:
| SKIP { Skip }
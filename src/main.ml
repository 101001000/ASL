open Parser
open AST
open ParseUtil
open Format

let input = Sys.argv.(1)

let string_of_dec (e: dec) : string =
  "var1 " ^ Camlcoq.camlstring_of_coqstring e ^ ";"

let string_of_decs (ds: dec list) : string =
  String.concat "\n" (List.map string_of_dec ds)

let string_of_expr (e: AST.expr) : string =
  string_of_int (to_int e)

let string_of_stmt (s: stmt) : string =
  match s with
  | Assign (d, e) -> 
    Printf.sprintf "%s := %s;" (Camlcoq.camlstring_of_coqstring d) (string_of_expr e)
  | Skip -> "SKIP;"

let string_of_stmts (ss: stmt list) : string =
  String.concat "\n" (List.map string_of_stmt ss)

let string_of_prog (p : prog) : string = match p with
  | Prog (ds, ss) -> string_of_decs ds ^ string_of_stmts ss

let main () =
	let buf = Lexing.from_string input in
		try
			let result = Parser.main Lexer.token buf in
				Printf.printf "%s\n" (string_of_prog result)
		with
		| Lexer.Error msg ->
			Printf.printf "lexer error %s\n" msg
		| Parser.Error ->
			Printf.printf "parse error %s \n" (Lexing.lexeme buf)
		;
		
	Printf.eprintf "t"
 


 

let _ = main ()
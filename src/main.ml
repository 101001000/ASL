open Ast
open Compiler
open LLVMAst

let of_str = Camlcoq.camlstring_of_coqstring
let to_int = Camlcoq.Z.to_int

let parse (s : string) : stmt =
  let lexbuf = Lexing.from_string s in
  let ast = Parser.prog Lexer.read lexbuf in
  ast

let print_ast_e (e : expr) : string = match e with
  | Lit n -> "Lit " ^ (string_of_int (to_int n))
  | Var x -> "Var " ^ (of_str x)

let rec print_ast_s (s : stmt) : string = match s with
  | Seq (s1, s2) -> "Seq (" ^ (print_ast_s s1) ^ ", " ^ (print_ast_s s2) ^ ")" 
  | Assign (x, e) -> "Ass (" ^ (of_str x) ^ ", " ^ (print_ast_e e) ^ ")"
  | Skip -> "Skip"

let print_code_e (e : expr) : string = match e with
  | Lit n -> (string_of_int (to_int n))
  | Var x -> (of_str x)

let rec print_code_s (s : stmt) : string = match s with
  | Seq (s1, s2) -> (print_code_s s1) ^ ";\n" ^ (print_code_s s2)
  | Assign (x, e) -> (of_str x) ^ " = " ^ (print_code_e e)
  | Skip -> ""


let parse_and_print_ast (str : string) : string =
  let st = parse str in
  print_ast_s st

let parse_and_print_code (str : string) : string =
  let st = parse str in
  print_code_s st

let output_file filename ast =
  let open Llvm_printer in
  let channel = open_out filename in
  toplevel_entities (Format.formatter_of_out_channel channel) ast;
  close_out channel


let () = 
	let code = "x = 4; y = 5; z = x" in
		print_endline("Working with: ");
		print_endline(code);
		print_endline("PP: ");
		print_endline(parse_and_print_code code);
		print_endline("AST: ");
		print_endline(parse_and_print_ast code);
		
		output_file "test.ll" (Compiler.compile (parse code))


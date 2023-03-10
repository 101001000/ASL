open Ast

let parse (s : string) : stmt =
  let lexbuf = Lexing.from_string s in
  let ast = Parser.prog Lexer.read lexbuf in
  ast

let print_ast_e (e : expr) : string = match e with
  | Lit n -> "Lit " ^ (string_of_int n)
  | Var x -> "Var " ^ x

let rec print_ast_s (s : stmt) : string = match s with
  | Seq (s1, s2) -> "Seq (" ^ (print_ast_s s1) ^ ", " ^ (print_ast_s s2) ^ ")" 
  | Assign (x, e) -> "Ass (" ^ x ^ ", " ^ (print_ast_e e) ^ ")"
  | Skip -> "Skip"

let print_code_e (e : expr) : string = match e with
  | Lit n -> (string_of_int n)
  | Var x -> x

let rec print_code_s (s : stmt) : string = match s with
  | Seq (s1, s2) -> (print_code_s s1) ^ ";\n" ^ (print_code_s s2)
  | Assign (x, e) -> x ^ " = " ^ (print_code_e e)
  | Skip -> ""


let parse_and_print_ast (str : string) : string =
  let st = parse str in
  print_ast_s st

let parse_and_print_code (str : string) : string =
  let st = parse str in
  print_code_s st


let () = print_endline(parse_and_print_code "x = 4; y = 3")


type expr =
  | Var of string
  | Lit of int
  
type stmt =
	| Seq of stmt * stmt
	| Assign of string * expr
	| Skip

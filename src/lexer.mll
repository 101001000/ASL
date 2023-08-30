{
  open Parser
  exception Error of string
}

let digit = ['0'-'9']
let letter_or_underscore = ['a'-'z' 'A'-'Z' '_']
let letter_or_underscore_or_digit = ['a'-'z' 'A'-'Z' '_' '0'-'9']

rule token = parse
| [' ' '\t' '\n'] 			              					  { token lexbuf }
| "var"                                   					  { VAR }
| '='                                     					  { EQ }
| ';'                                     					  { SEMI }
| letter_or_underscore letter_or_underscore_or_digit*  		  { ID(Lexing.lexeme lexbuf) }
| digit+ as i          				 	 					  { INT (Camlcoq.Z.of_sint32(Int32.of_string i)) }
| eof                                    					  { EOF }
| _
    { raise (Error (Printf.sprintf "At offset %d: unexpected character.\n" (Lexing.lexeme_start lexbuf))) }
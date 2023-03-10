{
open Parser
}

let white = [' ' '\t']+
let digit = ['0'-'9']
let int = '-'? digit+
let letter = ['a'-'z' 'A'-'Z']
let id = letter+

rule read = 
  parse
  | white { read lexbuf }
  | "=" { EQUALS }
  | ";" { SEMICOLON }
  | "skip" { SKIP }
  | id { ID (Lexing.lexeme lexbuf) }
  | int { LIT (int_of_string (Lexing.lexeme lexbuf)) }
  | eof { EOF }
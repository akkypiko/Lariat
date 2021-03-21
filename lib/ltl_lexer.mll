{
    open Ltl_parser

    (*let keywords =
      let tbl = Hashtbl.create 100 in
      List.iter (fun (k, t) -> Hashtbl.add tbl k t) [
      ];
      tbl*)
}

let space = [' ' '\r' '\t']+
let newline = '\r' | '\n' | "\r\n"
let integer = '0' | ['1'-'9']['0'-'9']*
let variable = ['a'-'z' '_']['A'-'Z' 'a'-'z' '0'-'9' '_']*

rule read = parse
  | space { read lexbuf }
  | newline { Lexing.new_line lexbuf; read lexbuf }
  | ";"      { read_comment lexbuf; read lexbuf }
  | "("      { LPAREN }
  | ")"      { RPAREN }
  | "!"      { BAN }
  | "&&"     { AND }
  | "||"     { OR }
  | "->"     { ARROW }
  | "True"   { TRUE }
  | "False"  { FALSE }
  | "X"      { NEXT }
  | "[]"     { GLOBALLY }
  | "G"      { GLOBALLY }
  | "<>"     { FUTURE }
  | "F"      { FUTURE }
  | "U"      { UNTIL }
  | "R"      { RELEASE }
  | "="      { EQ }
  | "<"      { LT }
  | "<="     { LE }
  | ">"      { GT }
  | ">="     { GE }
  | "+"      { PLUS }
  | "-"      { MINUS }
  | "*"      { STAR }
  | "/"      { SLASH }
  | "%"      { PERCENT }
  | integer  { INTEGER (int_of_string (Lexing.lexeme lexbuf)) }
  | variable { VAR (Lexing.lexeme lexbuf) }
  | eof      { EOF }
and read_comment = parse
  | newline { Lexing.new_line lexbuf }
  | eof { () }
  | _ { read_comment lexbuf }


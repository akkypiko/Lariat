{
    open System_parser

    let keywords =
      let tbl = Hashtbl.create 100 in
      List.iter (fun (k, t) -> Hashtbl.add tbl k t) [
        "var",    KW_VAR;
        "update", KW_UPDATE;
        "with",   KW_WITH;
        "else",   KW_ELSE;
      ];
      tbl
}

let space = [' ' '\r' '\t']+
let newline = '\r' | '\n' | "\r\n"
let integer = '0' | ['1'-'9']['0'-'9']*
let ident = ['a'-'z' '_']['A'-'Z' 'a'-'z' '0'-'9' '_']*

rule read = parse
  | space { read lexbuf }
  | newline { Lexing.new_line lexbuf; read lexbuf }
  | ";"      { read_comment lexbuf; read lexbuf }
  | "("      { LPAREN }
  | ")"      { RPAREN }
  | ","      { COMMA }
  | "|"      { PIPE }
  | "!"      { BAN }
  | "&&"     { AND }
  | "||"     { OR }
  | "->"     { ARROW }
  | "True"   { TRUE }
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
  | ident
    {
        let s = Lexing.lexeme lexbuf in
        try Hashtbl.find keywords s with Not_found -> VAR s
    }
  | eof      { EOF }
and read_comment = parse
  | newline { Lexing.new_line lexbuf }
  | eof { () }
  | _ { read_comment lexbuf }


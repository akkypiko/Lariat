%{
    open Ltl
%}

%token
  LPAREN RPAREN
  BAN AND OR ARROW
  TRUE FALSE
  NEXT GLOBALLY FUTURE UNTIL RELEASE
  EQ LT LE GT GE
  PLUS MINUS STAR SLASH PERCENT

%token <int>    INTEGER
%token <string> VAR
%token EOF

%right ARROW
%left OR
%left AND
(* %nonassoc UNTIL RELEASE *)
(* %nonassoc EQ LT LE GT GE *)
%left PLUS MINUS
%left STAR SLASH PERCENT
%right prec_uni


%start <Prop.arith Ltl.nn_t> parse

%%

parse:
  p=path_formula EOF
    { p }

path_formula:
  | LPAREN f=path_formula RPAREN
      { f }
  | f=atomic_proposition
      { ap f }
  | TRUE
      { true_ }
  | FALSE
      { false_ }
  | BAN f=path_formula
      %prec prec_uni
      { not_ f }
  | NEXT LPAREN f=path_formula RPAREN
      { next f }
  | GLOBALLY LPAREN f=path_formula RPAREN
      { globally f }
  | FUTURE LPAREN f=path_formula RPAREN
      { future f }
  | f=path_formula AND g=path_formula
      { and_ f g }
  | f=path_formula OR g=path_formula
      { or_ f g }
  | f=path_formula ARROW g=path_formula
      { implies f g }
  | LPAREN f=path_formula RPAREN UNTIL LPAREN g=path_formula RPAREN
      { until f g }
  | LPAREN f=path_formula RPAREN RELEASE LPAREN g=path_formula RPAREN
      { release f g }

atomic_proposition: a=arithmetic_proposition { a }

arithmetic_proposition:
  | x=expression EQ y=expression
      { AP_Eq (x, y) }
  | x=expression LT y=expression
      { AP_Lt (x, y) }
  | x=expression LE y=expression
      { AP_Le (x, y) }
  | x=expression GT y=expression
      { AP_Gt (x, y) }
  | x=expression GE y=expression
      { AP_Ge (x, y) }

expression:
  | LPAREN x=expression RPAREN
      { x }
  | x=INTEGER
      { EInt x }
  | x=VAR
      { EVar x }
  | x=expression PLUS y=expression
      { EAdd (x, y) }
  | x=expression MINUS y=expression
      { ESub (x, y) }
  | x=expression STAR y=expression
      { EMul (x, y) }
  | x=expression SLASH y=expression
      { EDiv (x, y) }
  | x=expression PERCENT y=expression
      { Prop.EMod (x, y) }

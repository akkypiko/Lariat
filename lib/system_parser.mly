%{
    open System
%}

%token
  KW_VAR KW_UPDATE KW_WITH KW_ELSE
  LPAREN RPAREN COMMA PIPE ARROW
  BAN AND OR
  TRUE
  EQ LT LE GT GE 
  PLUS MINUS STAR SLASH PERCENT 

%token <int>    INTEGER
%token <string> VAR
%token EOF

%left OR
%left AND
(* %nonassoc EQ LT LE GT GE *)
%left PLUS MINUS
%left STAR SLASH PERCENT
%right prec_uni


%start <System.transition_system> parse

%%

parse:
  vd=vars_decl ts_procs=list(var_update) EOF
    {
        let ts_location =
          vd
          |> List.mapi (fun i (x, _) -> i, x)
          |> List.fold_left (fun m (i, x) -> Prop.IdMap.add x i m) Prop.IdMap.empty
        in
        let ts_init =
          vd
          |> List.map snd
          |> Array.of_list
        in
        {
            ts_location;
            ts_init;
            ts_procs;
        }
    }


vars_decl:
  KW_VAR vis=separated_nonempty_list(COMMA, var_init)
    { vis }

var_init:
  x=VAR EQ v=INTEGER
    { x, v }

var_update:
  KW_UPDATE x=VAR KW_WITH option(PIPE) c=clause
    {
        let trans, el = c in
        x, trans, Option.value el ~default: (Prop.EVar x)
    }

clause:
  | e=else_update
      { [], Some e }
  | t=transition
      { [t], None }
  | t=transition PIPE c=clause
      { let c, e = c in (t :: c), e }

transition:
  tr_guard=boolean_formula ARROW tr_update=expression
    { { tr_guard; tr_update } }

else_update:
  KW_ELSE ARROW e=expression
    { e }

boolean_formula:
  | LPAREN f=boolean_formula RPAREN
      { f }
  | f=arithmetic_proposition
      { PArith f }
  | TRUE
      { PTrue }
  | BAN f=boolean_formula
      %prec prec_uni
      { PNot f }
  | f=boolean_formula AND g=boolean_formula
      { PAnd [f; g] }
  | f=boolean_formula OR g=boolean_formula
      { POr [f ; g] }

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

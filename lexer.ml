open Parser

type t_token = Parser.token * Lexing.position * Lexing.position

let dummy = ( EOF, Lexing.dummy_pos, Lexing.dummy_pos )

type state = { lb:Lexing.lexbuf; mutable last: t_token; }

let get_token lexbuf =
  let token = LexerCore.token lexbuf in
  let startp = lexbuf.Lexing.lex_start_p
  and endp = lexbuf.Lexing.lex_curr_p in
  token, startp, endp

let mk_state filename input =
  let lb = Lexing.from_channel input in
  lb.Lexing.lex_curr_p <- { lb.Lexing.lex_curr_p with Lexing.pos_fname = filename; };
  { lb; last=dummy; }

let get_next (state:state) : t_token =
  let rec aux () =
    match get_token state.lb with
    | END,st,ed -> USERPASS,st,ed
    | EOF,_,_ as tk -> tk
    | _,_,_ -> aux ()
  in
  let next = match get_token state.lb with
    | USERPASS,_,_ -> aux ()
    | tk -> tk
  in
  state.last <- next; next

let token_to_string = function
  | SIGMA ->      "SIGMA"
  | PI ->         "PI"
  | SET ->         "SET"
  | Q_UNION ->    "UNION"
  | Q_INTER ->    "INTER"
  | THEORY          -> "THEORY"
  | END            -> "END"
  | IS             -> "IS"
  | OR             -> "or"
  | MOD             -> "mod"
  | S_PARTIELLE     -> "+->>"
  | S_TOTALE        -> "-->>"
  | B_TOTALE        -> ">->>"
  | B_PARTIELLE        -> ">+>>"
  | NOT_S_INCLUDED  -> "/<<:"
  | MAPLET          -> "|->"
  | RELATION        -> "<->"
  | SOUSTRACTION_D  -> "<<|"
  | SOUSTRACTION_CO -> "|>>"
  | PARTIELLE       -> "+->"
  | TOTALE          -> "-->"
  | P_INJECTION     -> ">+>"
  | T_INJECTION     -> ">->"
  | EQUIV           -> "<=>"
  | S_INCLUDED      -> "<<:"
  | NOT_INCLUDED    -> "/<:"
  | RESTRICTION_Q   -> "\\|/"
  | RESTRICTION_T   -> "/|\\"
  | INSERTION_Q     -> "<-"
  | INSERTION_T     -> "->"
  | RESTRICTION_CO  -> "|>"
  | POWER           -> "**"
  | EMPTY_SET       -> "{}"
  | EMPTY_SEQ       -> "[]"
  | DOTDOT          -> ".."
  | B_UNION         -> "\\/"
  | B_INTER         -> "/\\"
  | DPRODUCT        -> "><"
  | PARALLEL        -> "||"
  | RESTRICTION_D   -> "<|"
  | SURCHARGE       -> "<+"
  | IMPLY           -> "=>"
  | NOT_EQUAL       -> "/="
  | NOT_MEMBER_OF   -> "/:"
  | INCLUDED        -> "<:"
  | SMALLER_OR_EQUAL -> "<="
  | GREATER_OR_EQUAL -> ">="
  | EQUALEQUAL      -> "=="
  | DIV             -> "/"
  | DOT             -> "."
  | SQUOTE          -> "\'"
  | BAR             -> "|"
  | LBRA            -> "{"
  | RBRA            -> "}"
  | TILDE           -> "~"
  | SEMICOLON       -> ";"
  | LSQU            -> "["
  | RSQU            -> "]"
  | PERCENT         -> "%"
  | AND             -> "&"
  | BANG            -> "!"
  | HASH            -> "#"
  | EQUAL           -> "="
  | MEMBER_OF       -> ":"
  | S_SMALLER       -> "<"
  | S_GREATER       -> ">"
  | PLUS            -> "+"
  | MINUS           -> "-"
  | STAR            -> "*"
  | COMMA           -> ","
  | RPAR            -> ")"
  | LPAR            -> "("
  | CIRC            -> "^"
  | QMARK            -> "?"
  | ANTISLASH -> "\\"
  | AFFECTATION -> ":="
  | RSHIFT -> ">>"
  | LSHIFT -> "<<<"
  | RPLUS -> "rplus"
  | RMINUS -> "rminus"
  | RDIV -> "rdiv"
  | RMUL -> "rmul"
  | RPOW -> "rpow"
  | RSIGMA -> "rSIGMA"
  | RPI -> "rPi"
  | RLE -> "rle"
  | RGE -> "rge"
  | RLT -> "rlt"
  | RGT -> "rgt"
  | NOT -> "not"
  | PBOOL -> "bool"
  | USERPASS -> "USERPASS"
  | BTRUE -> "btrue"
  | BFALSE -> "bfalse"
  | IDENT (lc,id) -> Printf.sprintf "IDENT(%s)" id
  | INTEGER i -> string_of_int i
  | EOF -> "__EOF__"

let get_last_token_str state =
  let (tk,_,_) = state.last in
  token_to_string tk

let get_current_pos state = state.lb.Lexing.lex_curr_p

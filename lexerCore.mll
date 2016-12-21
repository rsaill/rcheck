{
  open Lexing
  open Parser

  exception Error of Syntax.P.loc * string

  let int_of_int_lit (s:string) : int =
    if String.get s 0 = '-' then
      let l=String.length s in
      int_of_string (String.sub s 1 (l-1))
    else int_of_string s

let keywords = Hashtbl.create 137

let _ = List.iter (fun (name, keyword) ->
    Hashtbl.add keywords name keyword) [
    (*Binders*)
   "SIGMA"     , SIGMA;
   "PI"        , PI;
   "SET"       , SET;
   "UNION"     , Q_UNION;
   "INTER"     , Q_INTER;
   "SET"       , SET;
   (*Operators and binders on reals*)
   "rSIGMA"     , RSIGMA;
   "rPI"        , RPI;
   "rplus"      , RPLUS;
   "rminus"     , RMINUS;
   "rmul"       , RMUL;
   "rdiv"       , RDIV;
   "rpow"       , RPOW;
   "rle"        , RLE;
   "rge"        , RGE;
   "rlt"        , RLT;
   "rgt"        , RGT;
   (* Pmm keywords*)
   "END"        , END;
   "IS"         , IS;
   "THEORY"     , THEORY;
   "User_Pass"  , USERPASS;
   (* propositional operators *)
   "or"         , OR;
   "not"        , NOT;
   "bool"       , PBOOL;
   "btrue"      , BTRUE;
   "bfalse"     , BFALSE;
   (* operators on integers*)
   "mod"       , MOD;
  ]

let ident_to_token loc id =
  try Hashtbl.find keywords id
  with Not_found -> IDENT ( loc , id )

}

let space   = [' ' '\t']
let ident   = ['a'-'z' 'A'-'Z' '_']['a'-'z' 'A'-'Z' '0'-'9' '_' '$']*
let int_lit = ['0'-'9']+
let commented_line = "//" [^'\n']*
(* let ren_ident = ident ( '.' ident )+ *)
let def_file = '<' ['a'-'z' 'A'-'Z' '0'-'9' '_' '.']+ '>'

rule token = parse
  | space       { token lexbuf }
  | '\n'        { new_line lexbuf ; token lexbuf }
  | '\r'        { token lexbuf }
  | "/*"        { comment lexbuf }
  | commented_line     { token lexbuf }

  | "+->>"      { S_PARTIELLE  }
  | "-->>"      { S_TOTALE  }
  | ">->>"      { B_TOTALE  }
  | ">+>>"      { B_PARTIELLE  }
  | "/<<:"      { NOT_S_INCLUDED  }

  | "|->"       { MAPLET  }
  | "<->"       { RELATION  }
  | "<<|"       { SOUSTRACTION_D  }
  | "|>>"       { SOUSTRACTION_CO  }
  | "+->"       { PARTIELLE  }
  | "-->"       { TOTALE  }
  | ">+>"       { P_INJECTION  }
  | ">->"       { T_INJECTION  }
  | "<=>"       { EQUIV  }
  | "<<:"       { S_INCLUDED  }
  | "/<:"       { NOT_INCLUDED  }
  | "\\|/"      { RESTRICTION_Q  }
  | "/|\\"      { RESTRICTION_T  }
  | "<<<"       { LSHIFT  }

  | "<-"        { INSERTION_Q  }
  | "->"        { INSERTION_T  }
  | "|>"        { RESTRICTION_CO  }
  | "**"        { POWER  }
  | "{}"        { EMPTY_SET  }
  | "[]"        { EMPTY_SEQ  }
  | ".."        { DOTDOT  }
  | "\\/"       { B_UNION  }
  | "/\\"       { B_INTER  }
  | "><"        { DPRODUCT  }
  | "||"        { PARALLEL  }
  | "<|"        { RESTRICTION_D  }
  | "<+"        { SURCHARGE  }
  | "=>"        { IMPLY  }
  | "/="        { NOT_EQUAL  }
  | "/:"        { NOT_MEMBER_OF }
  | "<:"        { INCLUDED  }
  | "<="        { SMALLER_OR_EQUAL  }
  | ">="        { GREATER_OR_EQUAL  }
  | "=="        { EQUALEQUAL  }
  | ":="        { AFFECTATION }
  | ">>"        { RSHIFT }

  | '/'         { DIV  }
  | '.'         { DOT  }
  | '\''        { SQUOTE  }
  | '|'         { BAR  }
  | '{'         { LBRA  }
  | '}'         { RBRA   }
  | '~'         { TILDE  }
  | ';'         { SEMICOLON  }
  | '['         { LSQU  }
  | ']'         { RSQU  }
  | '%'         { PERCENT  }
  | '&'         { AND  }
  | '!'         { BANG  }
  | '#'         { HASH }
  | '='         { EQUAL  }
  | ':'         { MEMBER_OF  }
  | '<'         { S_SMALLER  }
  | '>'         { S_GREATER  }
  | '+'         { PLUS  }
  | '-'         { MINUS  }
  | '*'         { STAR  }
  | ','         { COMMA  }
  | ')'         { RPAR  }
  | '('         { LPAR  }
  | '^'         { CIRC  }
  | '?'         { QMARK }
  | '\\'         { ANTISLASH }

  | ident as id { ident_to_token lexbuf.Lexing.lex_start_p id }
  | int_lit as i  { INTEGER ( int_of_int_lit i ) }
  | _   as c    { raise (Error (lexbuf.Lexing.lex_start_p, "Unexpected character '" ^ String.make 1 c ^ "'.")) }
  | eof         { EOF }

 and comment = parse
  | "*/" { token lexbuf          }
  | '\n' { new_line lexbuf ; comment lexbuf }
  | _    { comment lexbuf        }
  | eof	 { raise (Error (lexbuf.Lexing.lex_start_p, "Unexpected end of file")) }

open Utils

let full_report = ref false

(* Parsing *)

module I = Parser.MenhirInterpreter

let loc_from_env env : Lexing.position =
  let (start,_) = I.positions env in
  start

let rec loop (state:Lexer.state) chkp =
  match chkp with
  | I.InputNeeded env -> loop state (I.offer chkp (Lexer.get_next state))
  | I.Shifting _
  | I.AboutToReduce _ -> loop state (I.resume chkp)
  | I.HandlingError env ->
    Failure (loc_from_env env,"Parsing error: unexpected token '"
                                    ^ Lexer.get_last_token_str state ^ "'.")
  | I.Accepted v -> Success v
  | I.Rejected -> assert false

let parse_file (fn:string) : Formula.r_theory list t_error =
  try
    let input = open_in fn in
    let state = Lexer.mk_state fn input in
    let checkpoint = Parser.Incremental.system (Lexer.get_current_pos state) in
    let theories = loop state checkpoint in
    close_in input; theories
  with
  | LexerCore.Error (p,msg) -> Failure (p,msg)
  | Sys_error msg -> Failure (Lexing.dummy_pos,msg)

(* Checking *)
let is_forward_theory (tname:string) : bool =
  if String.length tname >= 3 then
    ( String.compare "Gen" (String.sub tname 0 3) = 0 )
  else false

let check_rule (force_fwd:bool) (tname:string) (n:int) (r:Formula.r_rule) : unit =
  try
    let r = match Formula.to_rule r with 
      | Syntax.Backward (guards,hyps,goal) when force_fwd -> Syntax.Forward (guards,hyps,goal)
      | r -> r
    in
    ignore (Typing.check_rule r)
  with
  | Formula.Error (l,msg) -> Error.print l "Syntax error: %s" msg
  | Typing.Error (l,msg) -> Error.print l "Typing error: %s" msg

let check_theory (th:Formula.r_theory) : unit =
  if is_forward_theory th.Formula.tname then
   List.iteri (check_rule true th.Formula.tname) th.Formula.trules 
  else List.iteri (check_rule false th.Formula.tname) th.Formula.trules

let run_on_file (filename:string) : unit =
  match parse_file filename with
  | Success lst -> List.iter check_theory lst;
  | Failure (lc,msg) -> ( Error.print lc "%s" msg; exit(1) )

let args = [ 
  ( "--ignore-unknown-guards", Arg.Set Formula.ignore_unknown_guards, "Ignore Unknown Guards.")
]

let _ = Arg.parse args run_on_file ("Usage: "^ Sys.argv.(0) ^" [options] files")

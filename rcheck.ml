open Utils

let typing_only = ref false
let report_file = ref None

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

(* Report *)

let pp_loc out loc =
  let open Lexing in
  Printf.fprintf out "line %i, column %i in %s"
    loc.pos_lnum (loc.pos_cnum-loc.pos_bol+1) loc.pos_fname

let report_error (tname:string) (n:int) (l:Syntax.P.loc) (msg:string) : unit =
  match !report_file with
  | None -> ()
  | Some out ->
    begin
      Printf.fprintf out " ### RULE %s.%i\n" tname n; 
      Printf.fprintf out "ERROR MESSAGE: %s\n" msg; 
      Printf.fprintf out "ERROR LOCATION: %a\n" pp_loc l
    end

let report_ok (tname:string) (n:int) (tenv:Typing.typing_env) : unit =
  match !report_file with
  | None -> ()
  | Some out ->
    begin
      Printf.fprintf out " ### RULE %s.%i\n" tname n; 
      Typing.print_report out tenv
    end

(* Checking *)

let is_forward_theory (tname:string) : bool =
  if String.length tname >= 3 then
    ( String.compare "Gen" (String.sub tname 0 3) = 0 )
  else false

let check_rule_typing_only (force_fwd:bool) (r:Formula.r_rule) : unit =
  try 
    let r = match Formula.to_rule r with 
      | Syntax.P.Backward (guards,hyps,goal) when force_fwd ->
        Syntax.P.Forward (guards,hyps,goal)
      | r -> r
    in
    ignore (Typing.check_rule r)
  with
  | Formula.Error (l,msg) -> Error.print l "Syntax error: %s" msg
  | Typing.Error (l,msg) -> Error.print l "Typing error: %s" msg

let check_rule_with_report (force_fwd:bool) (tname:string) (n:int) (r:Formula.r_rule) : unit =
  try
    let r = match Formula.to_rule r with 
      | Syntax.P.Backward (guards,hyps,goal) when force_fwd ->
        Syntax.P.Forward (guards,hyps,goal)
      | r -> r
    in
    let (_,env) = Typing.check_rule r in
    Printf.fprintf stdout "RULE %s.%i [SYNTAX:OK] [TYPING:OK]\n" tname n;
    report_ok tname n env
  with
  | Formula.Error (l,msg) ->
    begin
      Printf.fprintf stdout "RULE %s.%i [SYNTAX:KO] [TYPING:NA]\n" tname n;
      report_error tname n l msg
    end
  | Typing.Error (l,msg) ->
    begin
      Printf.fprintf stdout "RULE %s.%i [SYNTAX:OK] [TYPING:KO]\n" tname n;
      report_error tname n l msg
    end

let check_rule (force_fwd:bool) (tname:string) (n:int) (r:Formula.r_rule) : unit =
    if !typing_only then check_rule_typing_only force_fwd r
    else check_rule_with_report force_fwd tname n r

let check_theory (th:Formula.r_theory) : unit =
  if is_forward_theory th.Formula.tname then
   List.iteri (check_rule true th.Formula.tname) th.Formula.trules 
  else List.iteri (check_rule false th.Formula.tname) th.Formula.trules

(* Main *)

let run_on_file (filename:string) : unit =
  match parse_file filename with
  | Success lst -> List.iter check_theory lst;
  | Failure (lc,msg) -> ( Error.print lc "%s" msg; exit(1) )

let set_report_file (f:string) : unit =
  report_file := Some (open_out f)

let args = [ 
  ( "--typing-only", Arg.Set typing_only, "Only report syntax and typing errors.");
  ( "-o", Arg.String set_report_file, "Output file for report.");
  ( "--ignore-unknown-guards", Arg.Set Formula.ignore_unknown_guards, "Ignore Unknown Guards.")
]

let _ = Arg.parse args run_on_file ("Usage: "^ Sys.argv.(0) ^" [options] files")

open Utils
open Syntax
open Syntax.P

type t_atom =
  | A_String of string
  | A_Integer of int
  | A_Empty_Set
  | A_Empty_Seq
  | A_Btrue
  | A_Bfalse
  | A_Other

type t_binder = Bang | Hash | Expr_B of expr_binder | Other_Binder | Set

type t_unary = Par | Squ | Bra | UMinus of loc | Tilde of loc | Not | Pbool

type t_binary =
    Application
  | Image
  | Substitution
  | Other_Binary
  | Antislash
  | Bar
  | Affectation
  | BinOp_Expr of loc*unit e_builtin
  | BinOp_Prop of prop_bop
  | BinOp_Pred of pred_bop
  | Pair of c_or_m

type formula =
  | F_Atom of loc*t_atom
  | F_Unary of loc*t_unary*formula
  | F_Binary of loc*t_binary*formula*formula
  | F_Binder of loc*t_binder*ident non_empty_list *formula

type t_goal =
  | Conclusion of formula
  | Equation of formula * formula

type r_rule = formula list * t_goal

type r_theory = { tloc:loc; tname:string; trules: r_rule list; }

exception Error of loc*string

let get_loc : formula -> loc = function
  | F_Atom (l,_)
  | F_Unary (l,_,_)
  | F_Binary (l,_,_,_)
  | F_Binder (l,_,_,_) -> l

type t_guard =
  | G_Not_Supported
  | G_band
  | G_bforward
  | G_bfresh
  | G_blvar
  | G_binhyp

type bi_t = E_BI of unit e_builtin | G_BI of t_guard

let keywords : (string,bi_t) Hashtbl.t = Hashtbl.create 137

let _ = List.iter (fun (name, keyword) ->
    Hashtbl.add keywords name keyword) [
   (* propositional operators *)
   "TRUE"       , E_BI TRUE;
   "FALSE"      , E_BI FALSE;
   (* Types *)
   "NAT"       , E_BI NAT;
   "NAT1"      , E_BI NAT1;
   "NATURAL"   , E_BI NATURAL;
   "NATURAL1"  , E_BI NATURAL1;
   "BOOL"      , E_BI BOOLEANS;
   "INTEGER"   , E_BI INTEGER;
   "INT"       , E_BI INT;
   "STRING"    , E_BI STRINGS;
   (* operators on integers*)
   "maxint"    ,E_BI MaxInt;
   "minint"    ,E_BI MinInt;
   "min"       ,E_BI Min;
   "max"       ,E_BI Max;
   "succ"      ,E_BI Successor;
   "pred"      ,E_BI Predecessor;
   (* guards *)
   "bvrb"      , G_BI G_Not_Supported;
   "bnot"      , G_BI G_Not_Supported;
   "bpattern"  , G_BI G_Not_Supported;
   "band"      , G_BI G_band;
   "bguard"    , G_BI G_Not_Supported;
   "bresult"   , G_BI G_Not_Supported;
   "bfresh"    , G_BI G_bfresh;
   "bnum"      , G_BI G_Not_Supported;
   "blvar"     , G_BI G_blvar;
   "btest"     , G_BI G_Not_Supported;
   "binhyp"    , G_BI G_binhyp;
   "bforward"   , G_BI G_bforward;
   "bcall"      , G_BI G_Not_Supported;
   "bsearch"    , G_BI G_Not_Supported;
   "bsubfrm"    , G_BI G_Not_Supported;
   "bmatch"     , G_BI G_Not_Supported;
   "bstring"    , G_BI G_Not_Supported;
   (* sets and relations *)
   "dom"        , E_BI Domain;
   "ran"        , E_BI Range;
   "id"         , E_BI Identity_Relation;
   "union"      , E_BI G_Union;
   "inter"      , E_BI G_Intersection;
   "prj1"       , E_BI First_Projection;
   "prj2"       , E_BI Second_Projection;
   "POW"        , E_BI (Power_Set Full);
   "POW1"       , E_BI (Power_Set Non_Empty);
   "card"       , E_BI Cardinal;
   "FIN"        , E_BI (Power_Set Finite);
   "FIN1"       , E_BI (Power_Set Finite_Non_Empty);
   "iterate"    , E_BI Iteration;
   "closure"    , E_BI Closure;
   "closure1"   , E_BI Transitive_Closure;
   "fnc"        , E_BI Fnc;
   "rel"        , E_BI Rel;
   (* sequences *)
   "seq"        , E_BI (Sequence_Set All_Seq);
   "seq1"       , E_BI (Sequence_Set Non_Empty_Seq);
   "iseq"       , E_BI (Sequence_Set Injective_Seq);
   "iseq1"      , E_BI (Sequence_Set Injective_Non_Empty_Seq);
   "perm"       , E_BI (Sequence_Set Permutations);
   "size"       , E_BI Size;
   "tail"       , E_BI Tail;
   "front"      , E_BI Front;
   "last"       , E_BI Last;
   "first"      , E_BI First;
   "rev"        , E_BI Reverse;
   "conc"       , E_BI G_Concatenation;
  ]

let is_builtin  (s:string) : bi_t option =
  try Some (Hashtbl.find keywords s)
  with Not_found -> None

type f_kind = E | P | U

let rec f_kind : formula -> f_kind = function
  | F_Atom (_,atm) ->
    begin match atm with
      | A_String s ->
        begin match is_builtin s with
          | Some _ -> E
          | _ -> U
        end
      | A_Integer _ | A_Empty_Set | A_Empty_Seq -> E
      | A_Btrue | A_Bfalse -> P
      | A_Other -> U
    end
  | F_Unary (_,u,fm) ->
    begin match u with
      | Par  -> f_kind fm
      | Pbool  | Squ | Bra | UMinus _ | Tilde _ -> E
      | Not  -> P
    end
  | F_Binary (_,op,f1,f2) ->
    begin match op with
      | Application -> E
      | Image -> E
      | Substitution -> f_kind f2
      | Other_Binary | Antislash | Bar | Affectation -> U
      | BinOp_Expr _ -> E
      | BinOp_Prop _ | BinOp_Pred _ -> P
      | Pair _ -> E
    end
  | F_Binder (_,(Hash|Bang),_,_) -> P
  | F_Binder (_,_,_,_) -> E

let rec formula_to_list : formula -> formula list = function
  | F_Binary (_,Pair Comma,hd,tl) -> hd::(formula_to_list tl)
  | fm -> [fm]

let to_ident : formula -> ident = function
  | F_Atom (l,A_String s) -> (l,s)
  | fm ->  raise (Error (get_loc fm,"identifier expected."))

let rec formula_to_ident_list : formula -> ident list = function
  | F_Binary (_,Pair Comma,hd,tl) -> (to_ident hd)::(formula_to_ident_list tl)
  | fm -> [to_ident fm]

let formula_to_ident_list_wp : formula -> ident list = function
  | F_Unary (_,Par,fm) -> formula_to_ident_list fm
  | fm -> [to_ident fm]

let rec to_expression : formula -> expression = function
  | F_Atom (l,atm) ->
    begin match atm with
      | A_String s ->
       begin match is_builtin s with
           | Some (E_BI bi) -> Builtin (l,bi)
           | Some _ -> raise (Error (l,"expression expected."))
           | None -> Ident (l,s)
       end
      | A_Integer i -> Builtin (l,Integer i)
      | A_Empty_Set -> Builtin (l,Empty_Set ())
      | A_Empty_Seq -> Builtin (l,Empty_Seq ())
      | A_Btrue | A_Bfalse -> raise (Error (l,"expression expected."))
      | A_Other -> raise (Error (l,"symbol not supported."))
    end
  | F_Unary (l,Bra,F_Binary (l2,Bar,f1,f2)) ->
    let lst = formula_to_ident_list f1 in
    Comprehension (l,(List.hd lst,List.tl lst),to_predicate f2)
  | F_Unary (l,op,fm) ->
    begin match op with
      | Par -> Parentheses (l,to_expression fm)
      | Squ ->
        let lst = List.map to_expression (formula_to_list fm) in
        Sequence (l,(List.hd lst,List.tl lst))
      | Bra ->
        let lst = List.map to_expression (formula_to_list fm) in
        Extension (l,(List.hd lst,List.tl lst))
      | UMinus l2 -> Application (l,Builtin (l2,Unary_Minus),to_expression fm)
      | Tilde l2 -> Application (l,Builtin (l2,Inverse_Relation),to_expression fm)
      | Pbool -> Pbool(l,to_predicate fm)
      | Not -> raise (Error (l,"expression expected."))
    end
  | F_Binary (l,op,f1,f2) ->
    begin
      match op with
      | Application ->
        Application(l,to_expression f1,to_expression f2)
      | Image ->
        Application(l,Builtin (l,Image),Couple (l,Infix,to_expression f1,to_expression f2))
      | Substitution ->
        begin match f1 with
          | F_Binary (l2,Affectation,f1_1,f1_2) -> Substitution (l,to_ident f1_1,to_expression f1_2,to_ident f2)
          | _ -> raise (Error (l,"unexpected formula."))
        end
      | Pair pt -> Couple (l,pt,to_expression f1,to_expression f2)
      | BinOp_Expr (l2,bi) ->
        Application(l,Builtin (l2,bi),Couple (l,Infix,to_expression f1,to_expression f2))
      | Affectation
      | Other_Binary -> raise (Error (l,"symbol not supported."))
      | BinOp_Prop _ | BinOp_Pred _ | Antislash | Bar ->
        raise (Error (l,"expression expected."))
    end
  | F_Binder (l,(Hash|Bang),_,_) -> raise (Error (l,"expression expected."))
  | F_Binder (l,Other_Binder,_,_) -> raise (Error (l,"symbol not supported."))
  | F_Binder (l,Expr_B bi,xlst,F_Unary(_,Par,F_Binary (_,Bar,f1,f2))) ->
    Binder (l,bi,xlst,to_predicate f1,to_expression f2)
  | F_Binder (l,Expr_B _,_,fm) -> raise (Error (get_loc fm,"symbol '|' expected."))
  | F_Binder (l,Set,xlst,fm) -> Comprehension (l,xlst,to_predicate fm)

and to_predicate : formula -> predicate = function
  | F_Atom (l,atm) ->
    begin match atm with
      | A_String s ->
        begin match is_builtin s with
          | Some _ -> raise (Error (l,"predicate expected."))
          | None -> P_Ident (l,s)
        end
      | A_Btrue -> P_Builtin (l,Btrue)
      | A_Bfalse -> P_Builtin (l,Bfalse)
      | A_Integer _
      | A_Empty_Set
      | A_Empty_Seq ->  raise (Error (l,"predicate expected."))
      | A_Other -> raise (Error (l,"symbol not supported."))
    end
  | F_Unary (l,op,fm) ->
    begin match op with
      | Par  -> Pparentheses (l,to_predicate fm)
      | Squ | Bra | UMinus _ | Tilde _ | Pbool ->
        raise (Error (l,"predicate expected."))
      | Not  -> Negation (l,to_predicate fm)
    end
  | F_Binary (l,op,f1,f2) ->
    begin
      match op with
      | Substitution ->
        begin match f1 with
          | F_Binary (l2,Affectation,f1_1,f1_2) ->
            P_Substitution (l,to_ident f1_1,to_expression f1_2,to_ident f2)
          | _ -> raise (Error (l,"unexpected formula."))
        end
      | Affectation | Other_Binary -> raise (Error (l,"symbol not supported."))
      | BinOp_Prop op -> Binary_Prop (l,op,to_predicate f1,to_predicate f2)
      | BinOp_Pred op -> Binary_Pred (l,op,to_expression f1,to_expression f2)
      | Application | Antislash | Bar | Image | Pair _ | BinOp_Expr _ ->
        raise (Error (l,"predicate expected."))
    end
  | F_Binder (l,Bang,lst,fm) -> Universal_Q (l,lst,to_predicate fm)
  | F_Binder (l,Hash,lst,fm) -> Existential_Q (l,lst,to_predicate fm)
  | F_Binder (l,_,_,_) -> raise (Error (l,"predicate expected."))

type to_guard_result =
  | Guard of guard list
  | IsFwd
  | NotAGuard

let is_joker s = String.length s = 1

let substract (id_lst1:ident list) (id_lst2:ident list) : ident list =
  let aux (id1:ident) : bool = not (List.exists (ident_eq id1) id_lst2) in
  List.filter aux id_lst1

let rec get_fvars : formula -> ident list = function
  | F_Atom (l,atm) ->
    begin match atm with
      | A_String s -> if is_joker s then [(l,s)] else []
      | A_Integer _ | A_Empty_Set | A_Empty_Seq | A_Btrue | A_Bfalse | A_Other -> []
    end
  | F_Unary (_,_,fm) -> get_fvars fm
  | F_Binary (_,_,f1,f2) -> (get_fvars f1)@(get_fvars f2)
  | F_Binder (_,_,(x,xlst),fm) -> substract (get_fvars fm) (x::xlst)

let ignore_unknown_guards = ref false

let rec to_guard : formula -> to_guard_result = function
  | F_Atom (l,atm) ->
    begin match atm with
     | A_String s ->
       begin match is_builtin s with
         | Some (G_BI G_bforward) -> IsFwd
         | Some (G_BI G_bfresh)
         | Some (G_BI G_blvar)
         | Some (G_BI G_band)
         | Some (G_BI G_binhyp) -> raise (Error (l,"this guard expects parameters."))
         | Some (G_BI G_Not_Supported) ->
           if !ignore_unknown_guards then Guard []
           else raise (Error (l,"this guard is not supported."))
         | _ -> NotAGuard
       end
     | A_Integer _ | A_Empty_Set | A_Empty_Seq | A_Btrue | A_Bfalse | A_Other
       -> NotAGuard
    end
  | F_Unary (l,op,fm) ->
    begin match op with
     | Par  -> to_guard fm
     | Squ | Bra | UMinus _ | Tilde _ | Not | Pbool  -> NotAGuard
    end
  | F_Binary (l,op,f1,f2) ->
    begin match op with
     | Application ->
       begin match f1 with
        | F_Atom (l2,A_String s) ->
          begin match is_builtin s with
            | Some (G_BI G_bforward) -> raise (Error (l,"incorrect number of parameters."))
            | Some (G_BI G_bfresh) ->
              begin match formula_to_list f2 with
                | [f2_1;f2_2;f2_3] -> Guard [Bfresh (l,to_ident f2_3,get_fvars f2_2)]
                | _ -> raise (Error (l,"The guard 'bfresh' expects three parameters."))
              end
            | Some (G_BI G_blvar) ->
              begin match formula_to_list f2 with
                | [f2_1] -> Guard [Blvar (l,to_ident f2_1)]
                | _ -> raise (Error (l,"The guard 'blvar' expects one parameter."))
              end
            | Some (G_BI G_binhyp) ->
              begin match formula_to_list f2 with
                | [f2_1] -> Guard [Binhyp (l,to_predicate f2_1)]
                | _ -> raise (Error (l,"The guard 'binhyp' expects one parameter."))
              end
            | Some (G_BI G_band) ->
              begin match formula_to_list f2 with
                | [f2_1;f2_2] ->
                  begin match to_guard f2_1, to_guard f2_2 with
                    | Guard lst1, Guard lst2 -> Guard (lst1@lst2)
                    | IsFwd, _ -> raise (Error (get_loc f2_1,"Unexpected guard bforward."))
                    | _, IsFwd -> raise (Error (get_loc f2_2,"Unexpected guard bforward."))
                    | NotAGuard, _ -> raise (Error (get_loc f2_1,"guard expected."))
                    | _, NotAGuard -> raise (Error (get_loc f2_2,"guard expected."))
                  end
                | _ -> raise (Error (l,"The guard 'band' expects two parameters."))
              end
            | Some (G_BI G_Not_Supported) ->
              if !ignore_unknown_guards then Guard []
              else raise (Error (l,"this guard is not supported."))
            | _ -> NotAGuard
          end
        | _ -> NotAGuard
       end
     | Antislash -> Guard [Bnfree (l,formula_to_ident_list_wp f1,get_fvars f2)]
     | Image | Substitution | Other_Binary | Bar | Affectation | BinOp_Expr _
     | BinOp_Prop _ | BinOp_Pred _ | Pair _ -> NotAGuard
    end
  | F_Binder _ -> NotAGuard

let to_guards_and_hyps (lst: formula list) : bool * guard list * predicate list =
  let rec aux (is_fwd,guards,hyps) fm =
    match to_guard fm with
    | Guard g -> (is_fwd,g@guards,hyps)
    | IsFwd -> (true,guards,hyps)
    | NotAGuard -> (is_fwd,guards,(to_predicate fm)::hyps)
  in
  List.fold_left aux (false,[],[]) lst

let to_rule (f_hyps,goal:r_rule) : rule =
  let (is_forward,guards,hyps) = to_guards_and_hyps f_hyps in
    match goal with
    | Conclusion fm ->
      if is_forward then Forward (guards,hyps,to_predicate fm)
      else Backward (guards,hyps,to_predicate fm)
    | Equation (lhs,rhs) ->
      begin match f_kind lhs, f_kind rhs with
          | E, E | E, U | U, E -> Rewrite_E (guards,hyps,to_expression lhs,to_expression rhs)
          | P, P | P, U | U, P -> Rewrite_P (guards,hyps,to_predicate lhs,to_predicate rhs)
          | P, E -> raise (Error (get_loc lhs,"this rule rewrites a predicate into an expression."))
          | E, P -> raise (Error (get_loc lhs,"this rule rewrites an expression into a predicate."))
          | U, U -> raise (Error (get_loc lhs,"cannot infer the kind of this rewrite rule (expression level or predicate level)."))
      end

let to_theory (th:r_theory) : theory =
  { tloc=th.tloc; tname=th.tname; trules=List.map to_rule th.trules; }

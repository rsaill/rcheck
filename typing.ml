open Btype
open Utils
open Syntax

exception Error of P.loc*string

let is_joker s = ( String.length s = 1 ) (*FIXME*)

module M = Map.Make(
  struct
    type t = string
    let compare = String.compare
  end )

module I = Map.Make(
  struct
    type t = int
    let compare = compare
  end )

(* *********************** GLOBAL CONTEXT *********************************** *)

module Global :
sig
  type t
  type context =  btype M.t * bool

  val create : (string list) M.t -> string option -> t
  val set_in_rw : t -> bool -> unit

  val new_meta : t -> btype
  val get_stype : t -> btype -> btype -> btype option

  val get_expr_type : t -> btype M.t -> P.ident -> btype
  val check_pred_usage : t -> btype M.t -> P.ident -> unit

  val freeze : t -> unit
  val normalize : t -> btype -> btype

  val pp : unit -> t -> string
  val context_to_string: t -> context -> string
  val iter : (string -> context -> btype option -> unit) -> t -> unit

  type diff_or_prod = Diff | Prod
  type constr = diff_or_prod * (P.expression*btype) * (P.expression*btype) * (P.expression*btype)
  val add_constraint : t -> constr -> unit
  val get_and_remove_constraints : t -> constr list
end = struct

  type context =  btype M.t * bool

  type diff_or_prod = Diff | Prod
  type constr = diff_or_prod * (P.expression*btype) * (P.expression*btype) * (P.expression*btype)

  type e_or_p =
    | E of context * btype
    | P of context

  type t = { mutable fvar: int;
             htbl: (string,e_or_p) Hashtbl.t;
             mutable subst: btype I.t;
             bnfree_inv: (string list) M.t;
             mutable in_rw: bool;
             blvar: string option;
             mutable constraints: constr list }

  let create bnfree_inv blvar = {
    fvar=0;
    htbl=Hashtbl.create 13;
    subst=I.empty;
    bnfree_inv=bnfree_inv;
    in_rw=false;
    blvar=blvar;
    constraints=[] }

  let set_in_rw (env:t) (in_rw:bool) =
    env.in_rw <- in_rw

  let new_meta (env:t) : btype =
    env.fvar <- env.fvar+1;
    T_Meta env.fvar

  let add_constraint (env:t) x =
    env.constraints <- x::env.constraints

  let get_and_remove_constraints (env:t) =
    let res = env.constraints in
    env.constraints <- []; res

  let rec normalize (s:t) : btype -> btype = function
    | T_INTEGER | T_BOOL | T_STRING | T_Set _ as ty -> ty
    | T_Power ty -> T_Power (normalize s ty)
    | T_Product (ty1,ty2) -> T_Product (normalize s ty1,normalize s ty2)
    | T_Meta m when I.mem m s.subst -> I.find m s.subst
    | T_Meta _ as ty -> ty

  let btype_eq (env:t) (ty1:btype) (ty2:btype) : bool =
    (normalize env ty1) = (normalize env ty2)

  let mk_context (env:t) (ctx:btype M.t) (id:string) : context =
    let vars_not_in_id: string list =
      try M.find id env.bnfree_inv with Not_found -> [] in
    let flt s _ = not (List.mem s vars_not_in_id) in
    let ctx_lst = M.filter flt ctx in
    let rw = env.in_rw && (
        match env.blvar with
        | None -> true
        | Some lv -> not (List.mem lv vars_not_in_id)
      ) in
    ( ctx_lst, rw )

  let context_eq (env:t) (map1,rw1:context) (map2,rw2:context) : bool =
    ( rw1 = rw2 ) && M.equal (btype_eq env) map1 map2

  let context_to_string (env:t) (map,rw:context) : string =
    let aux (s,ty) = "(" ^ s ^ ":"^Btype.to_string (normalize env ty)^")" in
    let s_lst = List.map aux (M.bindings map) in
    let s_lst =
      if rw then
        match env.blvar with
        | None -> ("(blvar(?):Unknown)")::s_lst
        | Some bl -> ("(blvar("^bl^"):Unknown)")::s_lst
      else s_lst
    in
    "[" ^ String.concat "" s_lst ^ "]"

  let get_expr_type (env:t) (ctx:btype M.t) (l,s:P.ident) : btype =
    try
      begin match Hashtbl.find env.htbl s with
        | E (m_ctx,ty) -> ty
        | P _ -> raise (Error (l,"expression expected; '"^s^"' is a predicate identifier."))
      end
    with Not_found ->
      if is_joker s then
        let ty = new_meta env in
        let m_ctx = mk_context env ctx s in
        ( Hashtbl.add env.htbl s (E (m_ctx,ty)); ty )
      else
        raise (Error (l,"unknown identifier '"^s^"'."))

  let check_pred_usage (env:t) (ctx:btype M.t) (l,s:P.ident) : unit =
    try
      begin match Hashtbl.find env.htbl s with
        | E _ -> raise (Error (l,"predicate expected; '"^s^"' is an expression identifier."))
        | P m_ctx ->
          let u_ctx = mk_context env ctx s in
          if context_eq env m_ctx u_ctx then ()
          else raise (Error(l,"the joker '"^s^"' is used in an unexpected context: Current context: "
                              ^ context_to_string env u_ctx
                              ^ ". Expected context: "
                              ^ context_to_string env m_ctx ^ "."))
      end
    with Not_found ->
      if is_joker s then ( Hashtbl.add env.htbl s (P (mk_context env ctx s)) )
      else raise (Error (l,"unknown identifier '"^s^"'."))

  let update_subst (env:t) (n:int) (rep:btype) : unit =
    env.subst <- I.map (Btype.subst n rep) env.subst;
    env.subst <- I.add n rep env.subst

  let rec get_stype (env:t) (t1:btype) (t2:btype) : btype option =
    match normalize env t1, normalize env t2 with
    | T_INTEGER, T_INTEGER -> Some T_INTEGER
    | T_BOOL, T_BOOL -> Some T_BOOL
    | T_STRING, T_STRING -> Some T_STRING
    | T_Set s1, T_Set s2 when s1=s2 -> Some (T_Set s1)
    | T_Power p1, T_Power p2 ->
      begin
        match get_stype env p1 p2 with
        | None -> None
        | Some p -> Some (T_Power p)
      end
    | T_Product (a1,b1), T_Product (a2,b2) ->
      begin
        match get_stype env a1 a2, get_stype env b1 b2 with
        | Some a, Some b -> Some (T_Product (a,b))
        | _, _ -> None
      end
    | T_Meta n, (T_Meta m as meta) when n=m -> Some meta
    | T_Meta n, ty | ty, T_Meta n ->
      if occurs n ty then None
      else (update_subst env n ty; Some ty)
    | _, _ -> None

  let rec meta_to_set = function
    | ( T_INTEGER | T_BOOL | T_STRING | T_Set _ ) as ty -> ty
    | T_Power ty -> T_Power (meta_to_set ty)
    | T_Product (ty1,ty2) -> T_Product (meta_to_set ty1,meta_to_set ty2)
    | T_Meta m -> T_Set ("#"^string_of_int m)

  let freeze (env:t) : unit =
    let freeze_type (ty:btype) : btype = meta_to_set (normalize env ty) in
    let freeze_context (map,rw) : context = (M.map freeze_type map,rw) in
    let aux (s:string) : e_or_p -> unit = function
      | P ctx -> Hashtbl.replace env.htbl s (P (freeze_context ctx))
      | E (ctx,ty) -> Hashtbl.replace env.htbl s (E (freeze_context ctx,freeze_type ty))
    in
    if env.constraints = [] then Hashtbl.iter aux env.htbl
    else raise (Error (P.dloc,"internal error: Global.freeze."))

  let pp () (env:t) : string =
    let aux (id:string) bp (str:string) : string =
      match bp with
      | E (_,ty) ->str ^ "("^id^" has type "^to_string ty^")"
      | P _ -> str ^ "("^id^" is a predicate)"
    in
    Hashtbl.fold aux env.htbl ""

  let iter (f:string -> context -> btype option -> unit) (env:t) : unit =
    let aux s = function
      | E (ctx,ty) -> f s ctx (Some ty)
      | P ctx -> f s ctx None
    in
    Hashtbl.iter aux env.htbl

end

(* *********************** LOCAL CONTEXT ************************************ *)

module Local :
sig
  type t
  val empty : t
  val declare : Global.t -> t -> P.ident -> t*btype
  val get : t -> P.ident -> btype
  val mem : t -> P.ident -> bool
  val fold : (string -> btype list -> 'a -> 'a) -> t -> 'a -> 'a
  val to_map : t -> btype M.t
end = struct

  type t = (btype list) M.t
  let empty = M.empty

  let get (ctx:t) (id:P.ident) : btype =
    try List.hd (M.find (snd id) ctx)
    with Not_found -> raise (Error (fst id,"unknown identifier '"^ snd id ^"'."))

  let mem (ctx:t) (id:P.ident) : bool = M.mem (snd id) ctx

  let declare (env:Global.t) (ctx:t) (id:P.ident) : t*btype =
    let ty = Global.new_meta env in
    if M.mem (snd id) ctx then
      let lst = M.find (snd id) ctx in
      (M.add (snd id) (ty::lst) ctx, ty)
    else
      (M.add (snd id) [ty] ctx, ty)

  let fold = M.fold

  let to_map (ctx:t) : btype M.t =
    let aux = function
      | [] -> assert false
      | ty::_ -> ty
    in
    M.map aux ctx

end

type typing_env = Global.t

(* *********************** ERROR MESSAGES *********************************** *)

let unexpected_type (env:Global.t) (e:P.expression) (inf:btype) (exp:btype) : 'a =
  let str = Printf.sprintf
      "this expression has type '%s' but an expression of type '%s' was expected."
      (to_string (Global.normalize env inf))
      (to_string (Global.normalize env exp)) in
  raise (Error (P.expr_loc e,str))

let integer_or_power_expected (env:Global.t) (e:P.expression) (ty:btype) : 'a =
  let str = Printf.sprintf "this expression has type '%s' but an expression of type INTEGER or POW(_) was expected."
      (Btype.to_string ty) in
  raise (Error (P.expr_loc e,str))

(* ********************************* MISC *********************************** *)

let ids_to_product (ctx:Local.t) ((hd,tl):P.ident non_empty_list) : btype =
  let aux pr id = T_Product (pr,Local.get ctx id) in
  List.fold_left aux (Local.get ctx hd) tl

let get_ident_type (env:Global.t) (ctx:Local.t) (id:P.ident) : btype =
  if Local.mem ctx id then Local.get ctx id
  else Global.get_expr_type env (Local.to_map ctx) id

(* ********************************* BUILTINS ******************************** *)

let get_builtin_type (env:Global.t) = function
  (* Booleans *)
  | TRUE | FALSE -> T_BOOL
  (* Integers *)
  | Integer _ | MaxInt | MinInt  -> T_INTEGER
  (* Arithmetic operators *)
  | Unary_Minus | Successor | Predecessor  -> type_of_func T_INTEGER T_INTEGER
  | Addition | Division | Modulo | Power  -> type_of_func2 T_INTEGER T_INTEGER T_INTEGER
  | Max | Min  -> type_of_func (T_Power T_INTEGER) T_INTEGER
  (* Types *)
  | NATURAL | NATURAL1 | INT | NAT | NAT1 | INTEGER  -> T_Power T_INTEGER
  | STRINGS  -> T_Power T_STRING
  | BOOLEANS  -> T_Power T_BOOL
  (* Empty set/sequence *)
  | Empty_Set  -> T_Power (Global.new_meta env)
  | Empty_Seq  -> type_of_func T_INTEGER (Global.new_meta env)
  (* Arithmetic or Set operator *)
  | Product  -> assert false
  | Difference -> assert false
  (* Operations on sets *)
  | Interval  -> type_of_func2 T_INTEGER T_INTEGER (T_Power T_INTEGER)
  | Intersection | Union  ->
    let t_set = T_Power (Global.new_meta env) in
    type_of_func2 t_set t_set t_set
  | First_Projection ->
    let mt1 = Global.new_meta env in
    let mt2 = Global.new_meta env in
    type_of_func2 (T_Power mt1) (T_Power mt2)
      (type_of_func (T_Product (mt1,mt2)) mt1)
  | Second_Projection ->
    let mt1 = Global.new_meta env in
    let mt2 = Global.new_meta env in
    type_of_func2 (T_Power mt1) (T_Power mt2)
      (type_of_func (T_Product (mt1,mt2)) mt2)
  | Parallel_Product ->
    let mt1 = Global.new_meta env in
    let mt2 = Global.new_meta env in
    let mt3 = Global.new_meta env in
    let mt4 = Global.new_meta env in
    type_of_func2 (type_of_func mt1 mt2) (type_of_func mt3 mt4)
      (T_Power (T_Product (T_Product (mt1,mt3),T_Product (mt2,mt4))))
  | Direct_Product ->
    let mt1 = Global.new_meta env in
    let mt2 = Global.new_meta env in
    let mt3 = Global.new_meta env in
    type_of_func2 (type_of_func mt1 mt2) (type_of_func mt1 mt3)
      (T_Power (T_Product (mt1,T_Product (mt2,mt3))))
  | Cardinal  -> type_of_func (T_Power (Global.new_meta env)) T_INTEGER
  | Power_Set _ ->
    let t_set = T_Power (Global.new_meta env) in
    type_of_func t_set (T_Power t_set)
  | G_Intersection | G_Union  ->
    let t_set = T_Power (Global.new_meta env) in
    type_of_func (T_Power t_set) t_set
  (* Operations on relations *)
  | Composition ->
    let ty1 = Global.new_meta env in
    let ty2 = Global.new_meta env in
    let ty3 = Global.new_meta env in
    type_of_func2 (type_of_func ty1 ty2) (type_of_func ty2 ty3) (type_of_func ty1 ty3)
  | Iteration ->
    let mt = Global.new_meta env in
    type_of_func2 (type_of_func mt mt) T_INTEGER (type_of_func mt mt)
  | Image  ->
    let t_arg = Global.new_meta env in
    let t_res = Global.new_meta env in
    type_of_func2 (type_of_func t_arg t_res) (T_Power t_arg) (T_Power t_res)
  | Domain_Restriction
  | Domain_Soustraction ->
    let mt1 = Global.new_meta env in
    let mt2 = Global.new_meta env in
    let ty_rel = type_of_func mt1 mt2 in
    let ty_dom = T_Power mt1 in
    type_of_func2 ty_dom ty_rel ty_rel
  | Codomain_Restriction
  | Codomain_Soustraction ->
    let mt1 = Global.new_meta env in
    let mt2 = Global.new_meta env in
    let ty_rel = type_of_func mt1 mt2 in
    let ty_ran = T_Power mt2 in
    type_of_func2 ty_rel ty_ran ty_rel
  | Surcharge  ->
    let ty_f = type_of_func (Global.new_meta env) (Global.new_meta env) in
    type_of_func2 ty_f ty_f ty_f
  | Relations | Functions _ ->
    let mt1 = Global.new_meta env in
    let mt2 = Global.new_meta env in
    type_of_func2 (T_Power mt1) (T_Power mt2) (T_Power (type_of_func mt1 mt2))
  | Identity_Relation  ->
    let mt = Global.new_meta env in
    type_of_func (T_Power mt) (type_of_func mt mt)
  | Inverse_Relation  ->
    let mt1 = Global.new_meta env in
    let mt2 = Global.new_meta env in
    type_of_func (type_of_func mt1 mt2) (type_of_func mt2 mt1)
  | Closure | Transitive_Closure ->
    let mt = Global.new_meta env in
    type_of_func (type_of_func mt mt) (type_of_func mt mt)
  | Domain  ->
    let t_arg = Global.new_meta env in
    let t_res = Global.new_meta env in
    type_of_func (type_of_func t_arg t_res) (T_Power t_arg)
  | Range  ->
    let t_arg = Global.new_meta env in
    let t_res = Global.new_meta env in
    type_of_func (type_of_func t_arg t_res) (T_Power t_res)
  | Fnc  ->
    let t_arg = Global.new_meta env in
    let t_res = Global.new_meta env in
    type_of_func (type_of_func t_arg t_res) (type_of_func t_arg (T_Power t_res))
  | Rel  ->
    let t_arg = Global.new_meta env in
    let t_res = Global.new_meta env in
    type_of_func (type_of_func t_arg (T_Power t_res)) (type_of_func t_arg t_res)
  (* Sequence operators *)
  | Sequence_Set _ ->
    let mt = Global.new_meta env in
    type_of_func (T_Power mt) (T_Power (type_of_seq mt))
  | Size  -> type_of_func (type_of_seq (Global.new_meta env)) T_INTEGER
  | First | Last  ->
    let mt = Global.new_meta env in
    type_of_func (type_of_seq mt) mt
  | Reverse | Front | Tail ->
    let t_seq = type_of_seq (Global.new_meta env) in
    type_of_func t_seq t_seq
  | Concatenation ->
    let t_seq = type_of_seq (Global.new_meta env) in
    type_of_func2 t_seq t_seq t_seq
  | Head_Insertion ->
    let mt = Global.new_meta env in
    let t_seq = type_of_seq mt in
    type_of_func2 mt t_seq t_seq
  | Tail_Insertion ->
    let mt = Global.new_meta env in
    let t_seq = type_of_seq mt in
    type_of_func2 t_seq mt t_seq
  | Head_Restriction | Tail_Restriction  ->
    let t_seq = type_of_seq (Global.new_meta env) in
    type_of_func2 t_seq T_INTEGER t_seq
  | G_Concatenation  ->
    let t_seq = type_of_seq (Global.new_meta env) in
    type_of_func (type_of_seq t_seq) t_seq

(* ********************************* EXPRESSIONS **************************** *)

let declare (env:Global.t) (ctx:Local.t) (id0,ids:P.ident non_empty_list) : Local.t * (btype*string) non_empty_list =
  let aux (ctx,lst:Local.t*(btype*string) list) (id:P.ident) : Local.t*(btype*string) list =
    let (ctx,ty) = Local.declare env ctx id in
    (ctx, (ty,snd id)::lst)
  in
  let (ctx,t_ids) = List.fold_left aux (ctx,[]) (id0::ids) in
  let t_ids = List.rev t_ids in
  (ctx, (List.hd t_ids,List.tl t_ids))

let rec type_expr (env:Global.t) (ctx:Local.t) : P.expression -> btype*T.expression = function
  | P.Ident  id ->
    let ty = get_ident_type env ctx id in ( ty, T.Var (ty,snd id) )

  | P.Builtin (l,bi) ->
    let ty = get_builtin_type env bi in (ty, T.Builtin (ty,bi) )

  | P.Pbool (_,p) -> let p = type_pred env ctx p in (T_BOOL, T.Pbool p)

  | P.Parentheses (_,e) -> type_expr env ctx e

  | P.Application (l,P.Builtin (l2,Product),P.Couple(_,P.Infix,e1,e2)) as e3 ->
    let (ty1,te1) = type_expr env ctx e1 in
    let (ty2,te2) = type_expr env ctx e2 in
    let mt = Global.new_meta env in
    let ty_prod = Btype.type_of_func2 ty1 ty2 mt in
    let _ = Global.add_constraint env (Global.Prod,(e1,ty1),(e2,ty2),(e3,mt)) in
    (mt, T.Application (T.Builtin (ty_prod,Product),T.Couple(te1,te2)))

  | P.Application (l,P.Builtin (_,Difference),P.Couple(_,P.Infix,e1,e2)) as e3 ->
    let (ty1,te1) = type_expr env ctx e1 in
    let (ty2,te2) = type_expr env ctx e2 in
    let mt = Global.new_meta env in
    let ty_diff = Btype.type_of_func2 ty1 ty2 mt in
    let _ = Global.add_constraint env (Global.Diff,(e1,ty1),(e2,ty2),(e3,mt)) in
    (mt, T.Application (T.Builtin (ty_diff,Difference),T.Couple(te1,te2)))

  | P.Application (l,e1,e2) ->
    let (ty_fun_inf,te1) = type_expr env ctx e1 in
    let ty_fun_exp = T_Power (T_Product (Global.new_meta env,Global.new_meta env)) in
    begin match Global.get_stype env ty_fun_inf ty_fun_exp with
      | Some (T_Power (T_Product (a,b))) ->
        let (ty_arg, te2) = type_expr env ctx e2 in
        ( match Global.get_stype env ty_arg a with
          | Some _ -> (b, T.Application (te1,te2))
          | None -> unexpected_type env e2 ty_arg a )
      | _ -> unexpected_type env e1 ty_fun_inf ty_fun_exp
    end

  | P.Couple (_,_,e1,e2) ->
    let (ty1,te1) = type_expr env ctx e1 in
    let (ty2,te2) = type_expr env ctx e2 in
    (T_Product (ty1,ty2), T.Couple (te1,te2))

  | P.Sequence  (_,(hd,tl)) ->
    let (ty_elt,te_hd) = type_expr env ctx hd in
    let aux (elt:P.expression) : T.expression =
      let (ty_inf,te_elt) = type_expr env ctx elt in
      match Global.get_stype env ty_inf ty_elt with
      | Some _ -> te_elt
      | None -> unexpected_type env hd ty_inf ty_elt
    in
    (Btype.type_of_seq ty_elt, T.Sequence (te_hd, List.map aux tl))

  | P.Extension (l,(hd,tl)) ->
    let (ty_elt,te_hd) = type_expr env ctx hd in
    let aux (elt:P.expression) : T.expression =
      let (ty_inf,te_elt) = type_expr env ctx elt in
      match Global.get_stype env ty_inf ty_elt with
      | Some _ -> te_elt
      | None -> unexpected_type env hd ty_inf ty_elt
    in
    (T_Power ty_elt, T.Extension (te_hd,List.map aux tl))

  | P.Comprehension (l,ids,p) ->
    let (ctx,t_ids) = declare env ctx ids in
    let pp = type_pred env ctx p in
    (T_Power (ids_to_product ctx ids), T.Comprehension (t_ids,pp))

  | P.Binder (l,bi,ids,p,e) ->
    begin match bi with
      | Sum | Prod ->
        let (ctx,t_ids) = declare env ctx ids in
        let pp = type_pred env ctx p in
        let (inf,ee) = type_expr env ctx e in
        begin match Global.get_stype env inf T_INTEGER with
          | Some _ -> (T_INTEGER, T.Binder (bi,t_ids,pp,ee))
          | None -> unexpected_type env e inf T_INTEGER
        end
      | Q_Union | Q_Intersection ->
        let (ctx,t_ids) = declare env ctx ids in
        let pp = type_pred env ctx p in
        let (ty_inf,ee) = type_expr env ctx e in
        let ty_exp = T_Power (Global.new_meta env) in
        begin match Global.get_stype env ty_inf ty_exp with
          | Some ty -> (ty,T.Binder (bi,t_ids,pp,ee))
          | _ -> unexpected_type env e ty_inf ty_exp
        end
      | Lambda ->
        let (ctx,t_ids) = declare env ctx ids in
        let pp = type_pred env ctx p in
        let (ty,ee) = type_expr env ctx e in
        (T_Power (T_Product (ids_to_product ctx ids, ty)),
         T.Binder (bi,t_ids,pp,ee))
    end
  | P.Substitution (l,_,_,_) -> raise (Error (l,"construct not supported."))

(* ********************************* PREDICATES ***************************** *)

and type_pred (env:Global.t) (ctx:Local.t) : P.predicate -> T.predicate = function
  | P.P_Builtin (_,P.Btrue) -> T.P_Builtin T.Btrue
  | P.P_Builtin (_,P.Bfalse) -> T.P_Builtin T.Bfalse

  | P.P_Ident id ->
    let _ = Global.check_pred_usage env (Local.to_map ctx) id in
    T.PVar (snd id)

  | P.Binary_Prop (l,op,p1,p2) ->
    let p1 = type_pred env ctx p1 in
    let p2 = type_pred env ctx p2 in
    T.Binary_Prop (op,p1,p2)

  | P.Binary_Pred (l,op,e1,e2) ->
    begin match op with
      | Equality | Disequality ->
        let (ty1,te1) = type_expr env ctx e1 in
        let (ty2,te2) = type_expr env ctx e2 in
        begin match Global.get_stype env ty1 ty2 with
          | Some _ -> T.Binary_Pred (op,te1,te2)
          | None -> unexpected_type env e2 ty1 ty2
        end
      | Membership | Non_Membership ->
        let (ty2,te2) = type_expr env ctx e2 in
        let (ty1,te1) = type_expr env ctx e1 in
        begin
          match Global.get_stype env (T_Power ty1) ty2 with
          | Some _ -> T.Binary_Pred (op,te1,te2)
          | None -> unexpected_type env e2 ty2 (T_Power ty1)
        end
      | Inclusion _ ->
        let ty0 = T_Power (Global.new_meta env) in
        let (ty1,te1) = type_expr env ctx e1 in
        let (ty2,te2) = type_expr env ctx e2 in
        begin match Global.get_stype env ty1 ty0 with
          | Some ty1_bis ->
            begin match Global.get_stype env ty1_bis ty2 with
              | Some _ -> T.Binary_Pred (op,te1,te2)
              | None -> unexpected_type env e2 ty2 ty1_bis
            end
          | None -> unexpected_type env e1 ty1 ty0
        end
      | Inequality _ ->
        let (ty1,te1) = type_expr env ctx e1 in
        let (ty2,te2) = type_expr env ctx e2 in
        begin match Global.get_stype env ty1 T_INTEGER with
          | Some _ ->
            begin match  Global.get_stype env ty2 T_INTEGER with
              | Some _ -> T.Binary_Pred (op,te1,te2)
              | None -> unexpected_type env e2 ty2 T_INTEGER
            end
          | None -> unexpected_type env e1 ty1 T_INTEGER
        end
    end

  | P.Negation (_,p) -> type_pred env ctx p
  | P.Pparentheses (_,p) -> type_pred env ctx p

  | P.Universal_Q (l,(id,[]),p) ->
    let (ctx,ty) = Local.declare env ctx id in
    let pp = type_pred env ctx p in
    T.Universal_Q (snd id,ty,pp)

  | P.Universal_Q (l,(id,hd::tl),p) ->
    let (ctx,ty) = Local.declare env ctx id in
    let pp = type_pred env ctx (P.Existential_Q (l,(hd,tl),p)) in
    T.Universal_Q (snd id,ty,pp)

  | P.Existential_Q (l,(id,[]),p) ->
    let (ctx,ty) = Local.declare env ctx id in
    let pp = type_pred env ctx p in
    T.Existential_Q (snd id,ty,pp)

  | P.Existential_Q (l,(id,hd::tl),p) ->
    let (ctx,ty) = Local.declare env ctx id in
    let pp = type_pred env ctx (P.Existential_Q (l,(hd,tl),p)) in
    T.Existential_Q (snd id,ty,pp)

  | P.P_Substitution (l,_,_,_) -> raise (Error (l,"construct not supported."))

(* *************** DELAYED TYPING CONSTRAINTS FOR '*' AND '-' *************** *)

type int_or_set_operation = Int_Op | Set_Op

let check_delayed_constraint (env:Global.t) (is_diff:Global.diff_or_prod)
    (is_int:int_or_set_operation) (e1,ty1) (e2,ty2) (e3,ty3) : unit =
  let type_diff_or_mult ty_exp =
    match Global.get_stype env ty1 ty_exp with
    | Some ty_exp ->
      begin match Global.get_stype env ty2 ty_exp with
        | Some ty_exp ->
          begin match Global.get_stype env ty3 ty_exp with
            | Some _ -> ()
            | None -> unexpected_type env e3 ty3 ty_exp
          end
        | None -> unexpected_type env e2 ty2 ty_exp
      end
    | None -> unexpected_type env e1 ty1 ty_exp
  in
  match is_int, is_diff with
  | Int_Op, _ -> type_diff_or_mult T_INTEGER (* Soustraction or Multiplication *)
  | Set_Op, Global.Diff ->
    type_diff_or_mult (T_Power (Global.new_meta env)) (* Set Difference *)
  | Set_Op, Global.Prod -> (*Cartesian Product*)
    let ty_exp = T_Power (Global.new_meta env) in
    begin match Global.get_stype env ty1 ty_exp with
      | Some (T_Power ty1_elt) ->
        let ty_exp = T_Power (Global.new_meta env) in
        begin match Global.get_stype env ty2 ty_exp with
          | Some (T_Power ty2_elt) ->
            let ty_exp = T_Power (T_Product (ty1_elt,ty2_elt)) in
            begin match Global.get_stype env ty3 ty_exp with
              | Some _ -> ()
              | None -> unexpected_type env e3 ty3 ty_exp
            end
          | Some _ -> assert false
          | None -> unexpected_type env e2 ty2 ty_exp
        end
      | Some _ -> assert false
      | None -> unexpected_type env e1 ty1 ty_exp
    end

let is_int_operation (env:Global.t) (e1,ty1:P.expression*btype)
    (e2,ty2:P.expression*btype) (e3,ty3:P.expression*btype) : int_or_set_operation =
  match ty1 with
  | T_Meta _ ->
    begin match ty2 with
      | T_Meta _ ->
        begin match ty3 with
          | T_Meta _ -> raise (Error (P.expr_loc e3,"cannot infer if this expression has type T_INTEGER of POW(_)."))
          | T_INTEGER -> Int_Op
          | T_Power _ -> Set_Op
          | _ -> integer_or_power_expected env e3 ty3
        end
      | T_INTEGER -> Int_Op
      | T_Power _ -> Set_Op
      | _ -> integer_or_power_expected env e2 ty2
    end
  | T_INTEGER -> Int_Op
  | T_Power _ -> Set_Op
  | _ -> integer_or_power_expected env e1 ty1

let check_delayed_constraints (env:Global.t) : unit =
  let aux (is_diff,(e1,m1),(e2,m2),(e3,m3)) =
    let c1 = (e1, Global.normalize env m1) in
    let c2 = (e2, Global.normalize env m2) in
    let c3 = (e3, Global.normalize env m3) in
    check_delayed_constraint env is_diff (is_int_operation env c1 c2 c3) c1 c2 c3
  in
  List.iter aux (List.rev (Global.get_and_remove_constraints env))

(* ************************** RULES  **************************************** *)

(* map(x) <- y@map(x) *)
let add_in_list (map:(string list) M.t) (x:string) (y:string list) : (string list) M.t =
  try
    let lst = M.find x map in
    M.add x (y@lst) map
  with Not_found -> M.add x y map

let read_guards (guards: P.guard list) :
  P.predicate list * (string list) M.t * P.ident list * string option =
  let rec aux (binhyps,bnfree,bfresh,blvar) = function
    | P.Binhyp (_,p) -> (p::binhyps,bnfree,bfresh,blvar)
    | P.Bfresh (_,y,lst) ->
      let bnfree = List.fold_left
          (fun map x -> add_in_list map (snd x) [snd y]) bnfree lst in
      (binhyps,bnfree,y::bfresh,blvar)
    | P.Blvar (l,id) ->
      begin match blvar with
        | None -> (binhyps,bnfree,bfresh,Some (snd id))
        | Some _ -> raise (Error (l,"the guard 'blvar' must be unique."))
      end
    | P.Bnfree (_,y,lst) ->
      let bnfree = List.fold_left
          (fun map x -> add_in_list map (snd x) (List.map snd y)) bnfree lst in
      (binhyps,bnfree,bfresh,blvar)
  in
  List.fold_left aux ( [], M.empty, [], None ) guards

let check_rule : P.rule -> Global.t = function
  | P.Backward (guards,hyps,goal) ->
    begin
      let (binhyps, bnfree, bfresh, blvar) = read_guards guards in
      let env = Global.create bnfree blvar in
      let _ = type_pred env Local.empty goal in
      let _ = List.iter (fun p -> ignore(type_pred env Local.empty p)) binhyps in
      let _ = check_delayed_constraints env in
      let _ = Global.freeze env in
      List.iter (fun p -> ignore(type_pred env Local.empty p)) hyps;
      env
    end
  | P.Forward (guards,hyps,goal) ->
    begin
      let (binhyps, bnfree, bfresh, blvar) = read_guards guards in
      let env = Global.create bnfree blvar in
      let _ = List.iter (fun p -> ignore(type_pred env Local.empty p)) binhyps in
      let _ = List.iter (fun p -> ignore(type_pred env Local.empty p)) hyps in
      let _ = check_delayed_constraints env in
      let _ = Global.freeze env in
      ignore (type_pred env Local.empty goal);
      env
    end
  | P.Rewrite_E (guards,hyps,lhs,rhs) ->
    begin
      let (binhyps, bnfree, bfresh, blvar) = read_guards guards in
      let env = Global.create bnfree blvar in
      let _ = Global.set_in_rw env true in
      let (ty_lhs,_) = type_expr env Local.empty lhs in
      let _ = Global.set_in_rw env false in
      let _ = List.iter (fun p -> ignore (type_pred env Local.empty p)) binhyps in
      let _ = check_delayed_constraints env in
      let _ = Global.freeze env in
      let _ = List.iter (fun p -> ignore(type_pred env Local.empty p)) hyps in
      let _ = Global.set_in_rw env true in
      let (ty_rhs,_) = type_expr env Local.empty rhs in
      match Global.get_stype env ty_lhs ty_rhs with
      | Some _ -> env
      | None -> unexpected_type env rhs ty_rhs ty_lhs
    end
  | P.Rewrite_P (guards,hyps,lhs,rhs) ->
    begin
      let (binhyps, bnfree, bfresh, blvar) = read_guards guards in
      let env = Global.create bnfree blvar in
      let _ = Global.set_in_rw env true in
      let _ = type_pred env Local.empty lhs in
      let _ = Global.set_in_rw env false in
      let _ = List.iter (fun p -> ignore(type_pred env Local.empty p)) binhyps in
      let _ = check_delayed_constraints env in
      let _ = Global.freeze env in
      let _ = List.iter (fun p -> ignore(type_pred env Local.empty p)) hyps in
      let _ = Global.set_in_rw env true in
      ignore (type_pred env Local.empty rhs);
      env
    end

(* ************************** REPORT **************************************** *)

let print_report (env:Global.t) : unit =
  let aux (jk:string) (ctx:Global.context) : btype option -> unit = function
    | None -> print_string ("The joker '"
                            ^ jk ^ "' is a predicate with context "
                            ^ Global.context_to_string env ctx ^ ".\n")
    | Some ty -> print_string ("The joker '"
                               ^ jk ^ "' is a expression of type '"^Btype.to_string ty^"' in context "
                               ^ Global.context_to_string env ctx ^ ".\n")
  in
  Global.iter aux env

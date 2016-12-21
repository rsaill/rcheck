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

(* *********************** LOCAL CONTEXT ************************************ *)

module Local :
sig
  type t
  val empty : t
  val declare : t -> P.ident -> Poly.btype -> t
  val get : t -> P.ident -> Poly.btype
  val mem : t -> P.ident -> bool
(*   val fold : (string -> btype -> 'a -> 'a) -> t -> 'a -> 'a *)
  val to_map : t -> Poly.btype M.t
end = struct

  type t = Poly.btype M.t
  let empty = M.empty

  let get (ctx:t) (id:P.ident) : Poly.btype =
    try M.find (snd id) ctx
    with Not_found -> raise (Error (fst id,"unknown identifier '"^ snd id ^"'."))

  let mem (ctx:t) (id:P.ident) : bool = M.mem (snd id) ctx

  let declare (ctx:t) (id:P.ident) (ty:Poly.btype) : t =
    M.add (snd id) ty ctx

(*   let fold = M.fold *)

  let to_map (ctx:t) : Poly.btype M.t = ctx

end

(* *********************** UNIFICATION CONTEXT *********************************** *)

module Unif :
sig
  type t
  val create : unit -> t
  val new_meta : t -> Poly.btype
  val get_stype : t -> Poly.btype -> Poly.btype -> Poly.btype option
  val normalize : t -> Poly.btype -> Poly.btype
end = struct

  type t = { mutable fvar: int; mutable subst: Poly.btype I.t }

  let create () : t = { fvar=0; subst=I.empty }

  let new_meta (env:t) : Poly.btype =
    env.fvar <- env.fvar+1;
    Poly.T_Meta env.fvar

  let rec normalize (s:t) (ty:Poly.btype) : Poly.btype =
    let open Poly in
    match ty with
    | T_INTEGER | T_BOOL | T_STRING | T_Set _ as ty -> ty
    | T_Power ty -> T_Power (normalize s ty)
    | T_Product (ty1,ty2) -> T_Product (normalize s ty1,normalize s ty2)
    | T_Meta m when I.mem m s.subst -> I.find m s.subst
    | T_Meta _ as ty -> ty

  let update_subst (env:t) (n:int) (rep:Poly.btype) : unit =
    env.subst <- I.map (Poly.subst n rep) env.subst;
    env.subst <- I.add n rep env.subst

  let rec get_stype (env:t) (t1:Poly.btype) (t2:Poly.btype) : Poly.btype option =
    let open Poly in
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

end

(* *********************** CONTEXT FOR GLOBAL FREE VARIABLES **************** *)

module FV_Context :
sig
  type t
  val create : (string list) M.t -> string option -> bool -> Local.t -> string -> t
  val equal : Unif.t -> t -> t -> bool
  val to_string : Unif.t -> t -> string
  val close_types : Unif.t -> t -> t
  val pp : out_channel -> t -> unit
end = struct

  type t =  Poly.btype M.t * bool * string option
  
  let create bnfree_inv blvar in_rw (ctx:Local.t) (id:string) : t =
    let vars_not_in_id: string list =
      try M.find id bnfree_inv with Not_found -> [] in
    let flt s _ = not (List.mem s vars_not_in_id) in
    let ctx_lst = M.filter flt (Local.to_map ctx) in
    let rw = in_rw && (
        match blvar with
        | None -> true
        | Some lv -> not (List.mem lv vars_not_in_id)
      ) in
    ( ctx_lst, rw , blvar)

  let btype_eq (env:Unif.t) (ty1:Poly.btype) (ty2:Poly.btype) : bool =
    (Unif.normalize env ty1) = (Unif.normalize env ty2)

  let opt_eq opt1 opt2 =
    match opt1, opt2 with
    | None, None -> true
    | Some s1, Some s2 -> String.equal s1 s2
    | _, _ -> false

  let equal (env:Unif.t) (map1,rw1,bv1:t) (map2,rw2,bv2:t) : bool =
    ( rw1 = rw2 ) && (opt_eq bv1 bv2) && M.equal (btype_eq env) map1 map2

  let to_string (unif:Unif.t) (map,rw,blvar:t) : string =
    let aux (s,ty) = "(" ^ s ^ ":"^Poly.to_string (Unif.normalize unif ty)^")" in
    let s_lst = List.map aux (M.bindings map) in
    let s_lst =
      if rw then
        match blvar with
        | None -> ("(blvar(?):Unknown)")::s_lst
        | Some bl -> ("(blvar("^bl^"):Unknown)")::s_lst
      else s_lst
    in
    "[" ^ String.concat "" s_lst ^ "]"

  let pp (out:out_channel) (map,rw,blvar:t) : unit =
    let aux (s,ty) = "(" ^ s ^ ":"^Poly.to_string ty^")" in
    let s_lst = List.map aux (M.bindings map) in
    let s_lst =
      if rw then
        match blvar with
        | None -> ("(blvar(?):Unknown)")::s_lst
        | Some bl -> ("(blvar("^bl^"):Unknown)")::s_lst
      else s_lst
    in
    Printf.fprintf out "[%s]" (String.concat "" s_lst)

  let close_types (unif:Unif.t) (map,rw,bv) : t =
    let close_type ty = Poly.close (Unif.normalize unif ty) in
    (M.map close_type map,rw,bv)
end

(* *********************** GLOBAL CONTEXT: COMMON PARTS ********************* *)

type op_kind = Set_Op | Int_Op | Unknown

module Global_Context_Common :
sig
  type t

  val new_meta : t -> Poly.btype
  val normalize : t -> Poly.btype -> Poly.btype
  val get_stype : t -> Poly.btype -> Poly.btype -> Poly.btype option

  type e_or_p =
    | E of FV_Context.t * Poly.btype
    | P of FV_Context.t 

  type constr =
    | Prod of (P.expression*Poly.btype) * (P.expression*Poly.btype) * (P.expression*Poly.btype)
    | Diff of (P.expression*Poly.btype) * (P.expression*Poly.btype) * (P.expression*Poly.btype)

  val create : (string list) M.t -> string option -> t
  val set_in_rw : t -> bool -> unit
  val get_unif : t -> Unif.t
  val get : t -> string -> e_or_p option
  val add_expr : t -> FV_Context.t -> string -> Poly.btype -> unit
  val add_pred : t -> FV_Context.t -> string -> unit

  val add_constraint : t -> constr -> unit
  val resolve_constraints : t -> unit
  val close : t -> unit

  val make_fv_context : t -> Local.t -> string -> FV_Context.t
  val are_fv_contexts_equal : t -> FV_Context.t -> FV_Context.t -> bool

  val to_map: t -> e_or_p M.t
end = struct

  type e_or_p =
    | E of FV_Context.t * Poly.btype
    | P of FV_Context.t 

  type constr =
    | Prod of (P.expression*Poly.btype) * (P.expression*Poly.btype) * (P.expression*Poly.btype)
    | Diff of (P.expression*Poly.btype) * (P.expression*Poly.btype) * (P.expression*Poly.btype)

  type t = { unif: Unif.t;
             htbl: (string,e_or_p) Hashtbl.t;
             bnfree_inv: (string list) M.t;
             mutable in_rw: bool;
             blvar: string option;
             mutable constraints: constr list }

  let get_unif env = env.unif
  let new_meta env = Unif.new_meta env.unif
  let normalize env = Unif.normalize env.unif
  let get_stype env = Unif.get_stype env.unif 

  let create (bnfree_inv:(string list) M.t) (blvar:string option) : t = {
    unif=Unif.create ();
    htbl=Hashtbl.create 13;
    bnfree_inv=bnfree_inv;
    in_rw=false;
    blvar=blvar;
    constraints=[] }

  let get (env:t) (id:string) : e_or_p option =
    try Some (Hashtbl.find env.htbl id)
    with Not_found -> None

  let add_expr (env:t) (ctx:FV_Context.t) (id:string) (ty:Poly.btype) : unit =
    Hashtbl.add env.htbl id (E (ctx,ty))

  let add_pred (env:t) (ctx:FV_Context.t) (id:string) : unit =
    Hashtbl.add env.htbl id (P ctx)

  let set_in_rw (env:t) (in_rw:bool) =
    env.in_rw <- in_rw

  let add_constraint (env:t) x =
    env.constraints <- x::env.constraints

  let unexpected_type (env:t) (e:P.expression) (inf:Poly.btype) (exp:Poly.btype) : 'a =
    let str = Printf.sprintf
        "this expression has type '%s' but an expression of type '%s' was expected."
        (Poly.to_string (normalize env inf))
        (Poly.to_string (normalize env exp)) in
    raise (Error (P.expr_loc e,str))

  let integer_or_power_expected (env:t) (e:P.expression) (ty:Poly.btype) : 'a =
    let str = Printf.sprintf "this expression has type '%s' but an expression of type INTEGER or POW(_) was expected."
        (Poly.to_string (normalize env ty)) in
    raise (Error (P.expr_loc e,str))

  let type_int_operation env (e1,ty1) (e2,ty2) (e3,ty3) : unit =
    match get_stype env ty1 Poly.T_INTEGER with
    | Some _ ->
      begin match get_stype env ty2 Poly.T_INTEGER with
        | Some _ ->
          begin match get_stype env ty3 Poly.T_INTEGER with
            | Some _ -> ()
            | None -> unexpected_type env e3 ty3 Poly.T_INTEGER
          end
        | None -> unexpected_type env e2 ty2 Poly.T_INTEGER
      end
    | None -> unexpected_type env e1 ty1 Poly.T_INTEGER

  let type_set_difference env (e1,ty1) (e2,ty2) (e3,ty3) : unit =
    let ty_exp = Poly.T_Power (new_meta env) in
    match get_stype env ty1 ty_exp with
    | Some ty_exp ->
      begin match get_stype env ty2 ty_exp with
        | Some ty_exp ->
          begin match get_stype env ty3 ty_exp with
            | Some _ -> ()
            | None -> unexpected_type env e3 ty3 ty_exp
          end
        | None -> unexpected_type env e2 ty2 ty_exp
      end
    | None -> unexpected_type env e1 ty1 ty_exp

  let type_cartesian_product env (e1,ty1) (e2,ty2) (e3,ty3) : unit =
    let ty_exp_1 = Poly.T_Power (new_meta env) in
    let ty_exp_2 = Poly.T_Power (new_meta env) in
    match get_stype env ty1 ty_exp_1 with
    | Some (Poly.T_Power ty_elt_1) ->
      begin match get_stype env ty2 ty_exp_2 with
        | Some (Poly.T_Power ty_elt_2) ->
          let exp = Poly.T_Power (Poly.T_Product (ty_elt_1,ty_elt_2)) in
          begin match get_stype env ty3 exp with
            | Some _ -> ()
            | None -> unexpected_type env e3 ty3 exp
          end
        | _ -> unexpected_type env e2 ty2 ty_exp_2
      end
    | _ -> unexpected_type env e1 ty1 ty_exp_1

  let discriminate (env:t) (e1,ty1) (e2,ty2) (e3,ty3) : op_kind =
    let open Poly in
    match normalize env ty1 with
    | T_INTEGER -> Int_Op
    | T_Power _ -> Set_Op
    | T_Meta _ ->
      begin match normalize env ty2 with
        | T_INTEGER -> Int_Op
        | T_Power _ -> Set_Op
        | T_Meta _ -> 
          begin match normalize env ty3 with
            | T_INTEGER -> Int_Op
            | T_Power _ -> Set_Op
            | T_Meta _ -> Unknown
            | ty3 -> integer_or_power_expected env e3 ty3
          end
        | ty2 -> integer_or_power_expected env e2 ty2
      end
    | ty1 -> integer_or_power_expected env e1 ty1

  let resolve_constraint (env:t) (cstr:constr) : unit =
   match cstr with 
     | Prod ((e1,ty1),(e2,ty2),(e3,ty3)) ->
       begin match discriminate env (e1,ty1) (e2,ty2) (e3,ty3) with
         | Int_Op -> type_int_operation env (e1,ty1) (e2,ty2) (e3,ty3)
         | Set_Op -> type_cartesian_product env (e1,ty1) (e2,ty2) (e3,ty3)
         | Unknown -> raise (Error (P.expr_loc e3,"cannot infer if this expression has type T_INTEGER of POW(_)."))
       end
     | Diff ((e1,ty1),(e2,ty2),(e3,ty3)) ->
       begin match discriminate env (e1,ty1) (e2,ty2) (e3,ty3) with
         | Int_Op -> type_int_operation env (e1,ty1) (e2,ty2) (e3,ty3)
         | Set_Op -> type_set_difference env (e1,ty1) (e2,ty2) (e3,ty3)
         | Unknown -> raise (Error (P.expr_loc e3,"cannot infer if this expression has type T_INTEGER of POW(_)."))
       end

  let resolve_constraints (env:t) =
    let () = List.iter (resolve_constraint env) env.constraints in
    env.constraints <- []

  let make_fv_context (env:t) (ctx:Local.t) (id:string) : FV_Context.t =
    FV_Context.create env.bnfree_inv env.blvar env.in_rw ctx id

  let are_fv_contexts_equal (env:t) : FV_Context.t -> FV_Context.t -> bool =
    FV_Context.equal env.unif

  let close (env:t) : unit =
    let close_type ty = Poly.close (Unif.normalize env.unif ty) in
    let aux (s:string) : e_or_p -> unit = function
      | P ctx ->
        Hashtbl.replace env.htbl s (P (FV_Context.close_types env.unif ctx))
      | E (ctx,ty) ->
        Hashtbl.replace env.htbl s (E (FV_Context.close_types env.unif ctx,close_type ty))
    in
    if env.constraints = [] then Hashtbl.iter aux env.htbl
    else failwith "Internal error in Typing.Global_Context_Common.close."

  let to_map (env: t) : e_or_p M.t =
    let aux k v map = M.add k v map in
    Hashtbl.fold aux env.htbl M.empty
end


(* *********************** CLOSED GLOBAL CONTEXT **************************** *)

module Closed_Global_Context :
sig
  type t

  val create : (string list) M.t -> string option -> t
  val set_in_rw : t -> bool -> unit

  val new_meta : t -> Poly.btype
  val normalize : t -> Poly.btype -> Poly.btype
  val get_stype : t -> Poly.btype -> Poly.btype -> Poly.btype option

  val get_expr_type : t -> Local.t -> P.ident -> Poly.btype
  val check_pred_usage : t -> Local.t -> P.ident -> unit
  val add_constraint : t -> Global_Context_Common.constr -> unit

  val of_global_common : Global_Context_Common.t -> t
  val to_global_common : t -> Global_Context_Common.t
end = struct

  type t = Global_Context_Common.t 

  let create = Global_Context_Common.create
  let set_in_rw = Global_Context_Common.set_in_rw

  let new_meta = Global_Context_Common.new_meta
  let normalize = Global_Context_Common.normalize
  let get_stype = Global_Context_Common.get_stype

  let add_constraint (env:t) (x:Global_Context_Common.constr) : unit =
    let e3 = match x with
      | Global_Context_Common.Diff (_,_,(e3,_))
      | Global_Context_Common.Prod (_,_,(e3,_)) -> e3
    in
    raise (Error (P.expr_loc e3,"cannot infer if this expression has type T_INTEGER of POW(_)."))

  let get_expr_type (env:t) (ctx:Local.t) (l,s:P.ident) : Poly.btype =
    let open Global_Context_Common in
    match get env s with
    | Some (E (ctx1,ty)) ->
      let ctx2 = make_fv_context env ctx s in
      if are_fv_contexts_equal env ctx1 ctx2 then ty
      else
        raise (Error(l,"the joker '"^s^"' is used in an unexpected context. Current context: "
                              ^ FV_Context.to_string (Global_Context_Common.get_unif env) ctx2
                              ^ ". Expected context: "
                              ^ FV_Context.to_string (Global_Context_Common.get_unif env) ctx1 ^ "."))
    | Some (P _) -> raise (Error (l,"expression expected; '"^s^"' is a predicate identifier."))
    | None -> raise (Error (l,"unknown identifier '"^s^"'."))

  let check_pred_usage (env:t) (ctx:Local.t) (l,s:P.ident) : unit =
    let open Global_Context_Common in
       match get env s with
        | Some (E _) -> raise (Error (l,"predicate expected; '"^s^"' is an expression identifier."))
        | Some (P ctx1) ->
          let ctx2 = make_fv_context env ctx s in
          if are_fv_contexts_equal env ctx1 ctx2 then ()
          else
            raise (Error(l,"the joker '"^s^"' is used in an unexpected context. Current context: "
                              ^ FV_Context.to_string (Global_Context_Common.get_unif env) ctx2
                              ^ ". Expected context: "
                              ^ FV_Context.to_string (Global_Context_Common.get_unif env) ctx1 ^ "."))
        | None -> raise (Error (l,"unknown identifier '"^s^"'."))

  let of_global_common (env:Global_Context_Common.t) : t =
    let () = Global_Context_Common.resolve_constraints env in
    let () = Global_Context_Common.close env in
    env

  let to_global_common (env:t) : Global_Context_Common.t = env
end

module Open_Global_Context :
sig
  type t

  val create : (string list) M.t -> string option -> t
  val set_in_rw : t -> bool -> unit

  val new_meta : t -> Poly.btype
  val normalize : t -> Poly.btype -> Poly.btype
  val get_stype : t -> Poly.btype -> Poly.btype -> Poly.btype option

  val get_expr_type : t -> Local.t -> P.ident -> Poly.btype
  val check_pred_usage : t -> Local.t -> P.ident -> unit
  val add_constraint : t -> Global_Context_Common.constr -> unit

  val to_global_common : t -> Global_Context_Common.t
end = struct

  type t = Global_Context_Common.t 

  let create = Global_Context_Common.create
  let set_in_rw = Global_Context_Common.set_in_rw

  let new_meta = Global_Context_Common.new_meta
  let normalize = Global_Context_Common.normalize
  let get_stype = Global_Context_Common.get_stype

  let add_constraint = Global_Context_Common.add_constraint

  let get_expr_type (env:t) (ctx:Local.t) (l,s:P.ident) : Poly.btype =
    let open Global_Context_Common in
    match get env s with
    | Some (E (ctx1,ty)) ->
      let ctx2 = make_fv_context env ctx s in
      if are_fv_contexts_equal env ctx1 ctx2 then ty
      else
        raise (Error(l,"the joker '"^s^"' is used in an unexpected context. Current context: "
                       ^ FV_Context.to_string (Global_Context_Common.get_unif env) ctx2
                       ^ ". Expected context: "
                       ^ FV_Context.to_string (Global_Context_Common.get_unif env) ctx1 ^ "."))
    | Some (P _) -> raise (Error (l,"expression expected; '"^s^"' is a predicate identifier."))
    | None ->
      if is_joker s then
        let ty = new_meta env in
        let () = add_expr env (make_fv_context env ctx s) s ty in ty
      else
        raise (Error (l,"unknown identifier '"^s^"'."))

  let check_pred_usage (env:t) (ctx:Local.t) (l,s:P.ident) : unit =
    let open Global_Context_Common in
       match get env s with
        | Some (E _) -> raise (Error (l,"predicate expected; '"^s^"' is an expression identifier."))
        | Some (P ctx1) ->
          let ctx2 = make_fv_context env ctx s in
          if are_fv_contexts_equal env ctx1 ctx2 then ()
          else
            raise (Error(l,"the joker '"^s^"' is used in an unexpected context. Current context: "
                              ^ FV_Context.to_string (Global_Context_Common.get_unif env) ctx2
                              ^ ". Expected context: "
                              ^ FV_Context.to_string (Global_Context_Common.get_unif env) ctx1 ^ "."))
        | None ->
          if is_joker s then add_pred env (make_fv_context env ctx s) s
          else raise (Error (l,"unknown identifier '"^s^"'."))

  let to_global_common (env:t) : Global_Context_Common.t = env
end

(* ********************************* BUILTINS ******************************* *)

let cast_builtin (ty:'t) : unit e_builtin -> 't e_builtin = function
  | Empty_Set _ -> Empty_Set ty
  | Empty_Seq _ -> Empty_Seq ty
  | TRUE | FALSE | Integer _ | MaxInt | MinInt | Unary_Minus | Successor
  | Predecessor | Addition | Division | Modulo | Power | Max | Min
  | NATURAL | NATURAL1 | INT | NAT | NAT1 | INTEGER | STRINGS | BOOLEANS
  | Product | Difference | Interval | Intersection | Union | First_Projection
  | Second_Projection | Parallel_Product | Direct_Product | Cardinal
  | Power_Set _ | G_Intersection | G_Union | Composition | Iteration | Image
  | Domain_Restriction | Domain_Soustraction | Codomain_Restriction
  | Codomain_Soustraction | Surcharge | Relations | Functions _
  | Identity_Relation | Inverse_Relation | Closure | Transitive_Closure
  | Domain | Range | Fnc | Rel | Sequence_Set _ | Size | First | Last | Reverse
  | Front | Tail | Concatenation | Head_Insertion | Tail_Insertion
  | Head_Restriction | Tail_Restriction | G_Concatenation as bi -> bi

(* ********************************* FUNCTOR ******************************** *)

module Make(
    Global:
      sig
        type t

        val new_meta : t -> Poly.btype
        val normalize : t -> Poly.btype -> Poly.btype
        val get_stype : t -> Poly.btype -> Poly.btype -> Poly.btype option

        val get_expr_type : t -> Local.t -> P.ident -> Poly.btype
        val check_pred_usage : t -> Local.t -> P.ident -> unit
        val add_constraint : t -> Global_Context_Common.constr -> unit
      end
  ) :
sig
  val type_expr : Global.t -> Local.t -> P.expression -> Poly.btype*T.p_expression
  val type_pred : Global.t -> Local.t -> P.predicate -> T.p_predicate
  val unexpected_type : Global.t -> P.expression -> Poly.btype -> Poly.btype -> 'a
end
= struct

  (* *********************** ERROR MESSAGES *********************************** *)

  let unexpected_type (env:Global.t) (e:P.expression) (inf:Poly.btype) (exp:Poly.btype) : 'a =
    let str = Printf.sprintf
        "this expression has type '%s' but an expression of type '%s' was expected."
        (Poly.to_string (Global.normalize env inf))
        (Poly.to_string (Global.normalize env exp)) in
    raise (Error (P.expr_loc e,str))

  let integer_or_power_expected (env:Global.t) (e:P.expression) (ty:Poly.btype) : 'a =
    let str = Printf.sprintf "this expression has type '%s' but an expression of type INTEGER or POW(_) was expected."
        (Poly.to_string (Global.normalize env ty)) in
    raise (Error (P.expr_loc e,str))

  (* ********************************* MISC *********************************** *)

  let get_builtin_type (env:Global.t) (bi:'t e_builtin ) =
    let open Poly in
    match bi with
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
    | Empty_Set _ -> T_Power (Global.new_meta env)
    | Empty_Seq _ -> type_of_func T_INTEGER (Global.new_meta env)
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

  let declare (env:Global.t) (ctx:Local.t) (id0,ids:P.ident non_empty_list) : Local.t * (Poly.btype*string) non_empty_list =
    let aux (ctx,lst:Local.t*(Poly.btype*string) list) (id:P.ident) : Local.t*(Poly.btype*string) list =
      let ty = Global.new_meta env in
      let ctx = Local.declare ctx id ty in
      (ctx, (ty,snd id)::lst)
    in
    let (ctx,t_ids) = List.fold_left aux (ctx,[]) (id0::ids) in
    let t_ids = List.rev t_ids in
    (ctx, (List.hd t_ids,List.tl t_ids))

  let ids_to_product (ctx:Local.t) ((hd,tl):P.ident non_empty_list) : Poly.btype =
    let aux pr id = Poly.T_Product (pr,Local.get ctx id) in
    List.fold_left aux (Local.get ctx hd) tl

  (* ********************************* EXPRESSIONS **************************** *)

  let discriminate (env:Global.t) (e1,ty1) (e2,ty2) : op_kind =
    let open Poly in
    match Global.normalize env ty1 with
    | T_INTEGER -> Int_Op
    | T_Power _ -> Set_Op
    | T_Meta _ ->
      begin match Global.normalize env ty2 with
        | T_INTEGER -> Int_Op
        | T_Power _ -> Set_Op
        | T_Meta _ -> Unknown
        | ty2 -> integer_or_power_expected env e2 ty2
      end
    | ty1 -> integer_or_power_expected env e1 ty1

  let type_int_operation env (e1,ty1) (e2,ty2) =
    match Global.get_stype env ty1 Poly.T_INTEGER with
    | Some _ ->
      begin match Global.get_stype env ty2 Poly.T_INTEGER with
        | Some _ -> Poly.T_INTEGER
        | None -> unexpected_type env e2 ty2 Poly.T_INTEGER
      end
    | None -> unexpected_type env e1 ty1 Poly.T_INTEGER

  let type_set_difference env (e1,ty1) (e2,ty2) =
    let ty_exp = Poly.T_Power (Global.new_meta env) in
    match Global.get_stype env ty1 ty_exp with
    | Some ty_exp ->
      begin match Global.get_stype env ty2 ty_exp with
        | Some ty_exp -> ty_exp
        | None -> unexpected_type env e2 ty2 ty_exp
      end
    | None -> unexpected_type env e1 ty1 ty_exp

  let type_cartesian_product env (e1,ty1) (e2,ty2) =
    let ty_exp_1 = Poly.T_Power (Global.new_meta env) in
    let ty_exp_2 = Poly.T_Power (Global.new_meta env) in
    match Global.get_stype env ty1 ty_exp_1 with
    | Some (Poly.T_Power ty_elt_1) ->
      begin match Global.get_stype env ty2 ty_exp_2 with
        | Some (Poly.T_Power ty_elt_2) ->
          Poly.T_Power (Poly.T_Product (ty_elt_1,ty_elt_2))
        | _ -> unexpected_type env e2 ty2 ty_exp_2
      end
    | _ -> unexpected_type env e1 ty1 ty_exp_1

  let rec type_expr (env:Global.t) (ctx:Local.t) : P.expression -> Poly.btype*T.p_expression = function
    | P.Ident id ->
      if Local.mem ctx id then (Local.get ctx id, T.BVar (snd id))
      else
        let ty = Global.get_expr_type env ctx id in
        ( ty, T.FVar (ty,snd id) )

    | P.Builtin (l,bi) ->
      let ty = get_builtin_type env bi in (ty, T.Builtin (cast_builtin ty bi) )

    | P.Pbool (_,p) -> let p = type_pred env ctx p in (Poly.T_BOOL, T.Pbool p)

    | P.Parentheses (_,e) -> type_expr env ctx e

    | P.Application (l,P.Builtin (l2,Product),P.Couple(_,P.Infix,e1,e2)) as e3 ->
      let (ty1,te1) = type_expr env ctx e1 in
      let (ty2,te2) = type_expr env ctx e2 in
      let te = T.Application (T.Builtin Product,T.Couple(te1,te2)) in
      begin match discriminate env (e1,ty1) (e2,ty2) with
        | Int_Op ->
          let ty = type_int_operation env (e1,ty1) (e2,ty2) in (ty,te)
        | Set_Op ->
          let ty = type_cartesian_product env (e1,ty1) (e2,ty2) in (ty,te)
        | Unknown ->
          let mt = Global.new_meta env in
          let cstr = Global_Context_Common.Prod ((e1,ty1),(e2,ty2),(e3,mt)) in
          let () = Global.add_constraint env cstr in
          (mt, te)
      end

    | P.Application (l,P.Builtin (_,Difference),P.Couple(_,P.Infix,e1,e2)) as e3 ->
      let (ty1,te1) = type_expr env ctx e1 in
      let (ty2,te2) = type_expr env ctx e2 in
      let te = T.Application (T.Builtin Difference,T.Couple(te1,te2)) in
      begin match discriminate env (e1,ty1) (e2,ty2) with
        | Int_Op ->
          let ty = type_int_operation env (e1,ty1) (e2,ty2) in (ty,te)
        | Set_Op ->
          let ty = type_set_difference env (e1,ty1) (e2,ty2) in (ty,te)
        | Unknown ->
          let mt = Global.new_meta env in
          let cstr = Global_Context_Common.Diff ((e1,ty1),(e2,ty2),(e3,mt)) in
          let () = Global.add_constraint env cstr in
          (mt, te)
      end
      
    | P.Application (l,e1,e2) ->
      let open Poly in
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
      (Poly.T_Product (ty1,ty2), T.Couple (te1,te2))

    | P.Sequence  (_,(hd,tl)) ->
      let (ty_elt,te_hd) = type_expr env ctx hd in
      let aux (elt:P.expression) : T.p_expression =
        let (ty_inf,te_elt) = type_expr env ctx elt in
        match Global.get_stype env ty_inf ty_elt with
        | Some _ -> te_elt
        | None -> unexpected_type env hd ty_inf ty_elt
      in
      (Poly.type_of_seq ty_elt, T.Sequence (te_hd, List.map aux tl))

    | P.Extension (l,(hd,tl)) ->
      let (ty_elt,te_hd) = type_expr env ctx hd in
      let aux (elt:P.expression) : T.p_expression =
        let (ty_inf,te_elt) = type_expr env ctx elt in
        match Global.get_stype env ty_inf ty_elt with
        | Some _ -> te_elt
        | None -> unexpected_type env hd ty_inf ty_elt
      in
      (Poly.T_Power ty_elt, T.Extension (te_hd,List.map aux tl))

    | P.Comprehension (l,ids,p) ->
      let (ctx,t_ids) = declare env ctx ids in
      let pp = type_pred env ctx p in
      (Poly.T_Power (ids_to_product ctx ids), T.Comprehension (t_ids,pp))

    | P.Binder (l,bi,ids,p,e) ->
      begin match bi with
        | Sum | Prod ->
          let (ctx,t_ids) = declare env ctx ids in
          let pp = type_pred env ctx p in
          let (inf,ee) = type_expr env ctx e in
          begin match Global.get_stype env inf Poly.T_INTEGER with
            | Some _ -> (Poly.T_INTEGER, T.Binder (bi,t_ids,pp,ee))
            | None -> unexpected_type env e inf Poly.T_INTEGER
          end
        | Q_Union | Q_Intersection ->
          let (ctx,t_ids) = declare env ctx ids in
          let pp = type_pred env ctx p in
          let (ty_inf,ee) = type_expr env ctx e in
          let ty_exp = Poly.T_Power (Global.new_meta env) in
          begin match Global.get_stype env ty_inf ty_exp with
            | Some ty -> (ty,T.Binder (bi,t_ids,pp,ee))
            | _ -> unexpected_type env e ty_inf ty_exp
          end
        | Lambda ->
          let (ctx,t_ids) = declare env ctx ids in
          let pp = type_pred env ctx p in
          let (ty,ee) = type_expr env ctx e in
          (Poly.T_Power (Poly.T_Product (ids_to_product ctx ids, ty)),
           T.Binder (bi,t_ids,pp,ee))
      end
    | P.Substitution (l,_,_,_) -> raise (Error (l,"construct not supported."))

  (* ********************************* PREDICATES ***************************** *)

  and type_pred (env:Global.t) (ctx:Local.t) : P.predicate -> T.p_predicate = function
    | P.P_Builtin (_,P.Btrue) -> T.P_Builtin T.Btrue
    | P.P_Builtin (_,P.Bfalse) -> T.P_Builtin T.Bfalse

    | P.P_Ident id ->
      let _ = Global.check_pred_usage env ctx id in
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
            match Global.get_stype env (Poly.T_Power ty1) ty2 with
            | Some _ -> T.Binary_Pred (op,te1,te2)
            | None -> unexpected_type env e2 ty2 (Poly.T_Power ty1)
          end
        | Inclusion _ ->
          let ty0 = Poly.T_Power (Global.new_meta env) in
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
          begin match Global.get_stype env ty1 Poly.T_INTEGER with
            | Some _ ->
              begin match  Global.get_stype env ty2 Poly.T_INTEGER with
                | Some _ -> T.Binary_Pred (op,te1,te2)
                | None -> unexpected_type env e2 ty2 Poly.T_INTEGER
              end
            | None -> unexpected_type env e1 ty1 Poly.T_INTEGER
          end
      end

    | P.Negation (_,p) -> type_pred env ctx p
    | P.Pparentheses (_,p) -> type_pred env ctx p

    | P.Universal_Q (l,(id,[]),p) ->
      let ty = Global.new_meta env in
      let ctx = Local.declare ctx id ty in
      let pp = type_pred env ctx p in
      T.Universal_Q (snd id,ty,pp)

    | P.Universal_Q (l,(id,hd::tl),p) ->
      let ty = Global.new_meta env in
      let ctx = Local.declare ctx id ty in
      let pp = type_pred env ctx (P.Existential_Q (l,(hd,tl),p)) in
      T.Universal_Q (snd id,ty,pp)

    | P.Existential_Q (l,(id,[]),p) ->
      let ty = Global.new_meta env in
      let ctx = Local.declare ctx id ty in
      let pp = type_pred env ctx p in
      T.Existential_Q (snd id,ty,pp)

    | P.Existential_Q (l,(id,hd::tl),p) ->
      let ty = Global.new_meta env in
      let ctx = Local.declare ctx id ty in
      let pp = type_pred env ctx (P.Existential_Q (l,(hd,tl),p)) in
      T.Existential_Q (snd id,ty,pp)

    | P.P_Substitution (l,_,_,_) -> raise (Error (l,"construct not supported."))
end

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

type typing_env = Global_Context_Common.e_or_p M.t

let to_typing_env (env:Closed_Global_Context.t) : typing_env =
  let env = Closed_Global_Context.to_global_common env in
  let () = Global_Context_Common.close env in
  Global_Context_Common.to_map env

let builtin_map (f:'a -> 'b) : 'a e_builtin -> 'b e_builtin = function
  | Empty_Set x -> Empty_Set (f x)
  | Empty_Seq x -> Empty_Seq (f x)
  | TRUE | FALSE | Integer _ | MaxInt | MinInt | Unary_Minus | Successor
  | Predecessor | Addition | Division | Modulo | Power | Max | Min
  | NATURAL | NATURAL1 | INT | NAT | NAT1 | INTEGER | STRINGS | BOOLEANS
  | Product | Difference | Interval | Intersection | Union | First_Projection
  | Second_Projection | Parallel_Product | Direct_Product | Cardinal
  | Power_Set _ | G_Intersection | G_Union | Composition | Iteration | Image
  | Domain_Restriction | Domain_Soustraction | Codomain_Restriction
  | Codomain_Soustraction | Surcharge | Relations | Functions _
  | Identity_Relation | Inverse_Relation | Closure | Transitive_Closure
  | Domain | Range | Fnc | Rel | Sequence_Set _ | Size | First | Last | Reverse
  | Front | Tail | Concatenation | Head_Insertion | Tail_Insertion
  | Head_Restriction | Tail_Restriction | G_Concatenation as bi -> bi

let to_mono (env:Closed_Global_Context.t) (ty:Poly.btype) : Mono.btype =
  Mono.close (Closed_Global_Context.normalize env ty)

let rec to_m_expr (env:Closed_Global_Context.t) : T.p_expression -> T.m_expression = function
  | T.FVar (ty,id) -> T.FVar (to_mono env ty,id)
  | T.BVar _ as bv -> bv
  | T.Const (ty,id) -> T.Const (to_mono env ty,id)
  | T.Builtin bi -> T.Builtin (builtin_map (to_mono env) bi)
  | T.Pbool p -> T.Pbool (to_m_pred env p)
  | T.Application (f,a) -> T.Application (to_m_expr env f,to_m_expr env a)
  | T.Couple (a,b) -> T.Couple (to_m_expr env a,to_m_expr env b)
  | T.Sequence (hd,tl) -> T.Sequence (to_m_expr env hd,List.map (to_m_expr env) tl)
  | T.Extension (hd,tl) -> T.Extension (to_m_expr env hd,List.map (to_m_expr env) tl)
  | T.Comprehension ((hd,tl),p) ->
    let aux (ty,id)= (to_mono env ty,id) in
    T.Comprehension ((aux hd,List.map aux tl),to_m_pred env p)
  | T.Binder (bi,(hd,tl),p,e) ->
    let aux (ty,id)= (to_mono env ty,id) in
   T.Binder (bi,(aux hd,List.map aux tl),to_m_pred env p,to_m_expr env e)

and to_m_pred (env:Closed_Global_Context.t) : T.p_predicate -> T.m_predicate = function
  | T.PVar _ as pv -> pv
  | T.P_Builtin _ as bi -> bi
  | T.Binary_Prop (op,p,q) -> T.Binary_Prop(op,to_m_pred env p,to_m_pred env q)
  | T.Binary_Pred (op,e1,e2) -> T.Binary_Pred (op,to_m_expr env e1,to_m_expr env e2)
  | T.Negation p -> T.Negation (to_m_pred env p)
  | T.Universal_Q (id,ty,p) -> T.Universal_Q (id,to_mono env ty,to_m_pred env p)
  | T.Existential_Q (id,ty,p) -> T.Existential_Q (id,to_mono env ty,to_m_pred env p)

module TypeInference = Make(Open_Global_Context)
module TypeChecking = Make(Closed_Global_Context)

let close (env:Open_Global_Context.t) : Closed_Global_Context.t =
  Closed_Global_Context.of_global_common (Open_Global_Context.to_global_common env)

let check_rule : P.rule -> T.rule*typing_env = function
  | P.Backward (guards,hyps,goal) ->
    begin
      let (binhyps, bnfree, bfresh, blvar) = read_guards guards in
      (*Step 1: infer*)
      let env = Open_Global_Context.create bnfree blvar in
      let goal = TypeInference.type_pred env Local.empty goal in
      let binhyps = List.map (TypeInference.type_pred env Local.empty) binhyps in
      (*Step 2: check*)
      let env = close env in
      let hyps = List.map (TypeChecking.type_pred env Local.empty) hyps in
      (* --- *)
      (T.Backward (List.map (to_m_pred env) binhyps,
                   List.map (to_m_pred env) hyps,
                   to_m_pred env goal),
       to_typing_env env)
    end
  | P.Forward (guards,hyps,goal) ->
    begin
      let (binhyps, bnfree, bfresh, blvar) = read_guards guards in
      (*Step 1: infer*)
      let env = Open_Global_Context.create bnfree blvar in
      let binhyps = List.map (TypeInference.type_pred env Local.empty) binhyps in
      let hyps = List.map (TypeInference.type_pred env Local.empty) hyps in
      (*Step 2: check*)
      let env = close env in
      let goal = TypeChecking.type_pred env Local.empty goal in
      (* --- *)
      (T.Forward (List.map (to_m_pred env) binhyps,
                  List.map (to_m_pred env) hyps,
                  to_m_pred env goal),
       to_typing_env env)
    end
  | P.Rewrite_E (guards,hyps,lhs,rhs) ->
    begin
      let (binhyps, bnfree, bfresh, blvar) = read_guards guards in
      (*Step 1: infer*)
      let env = Open_Global_Context.create bnfree blvar in
      let () = Open_Global_Context.set_in_rw env true in
      let (ty_lhs,lhs2) = TypeInference.type_expr env Local.empty lhs in
      let () = Open_Global_Context.set_in_rw env false in
      let binhyps = List.map (TypeInference.type_pred env Local.empty) binhyps in
      (*Step 2: check*)
      let env = close env in
      let hyps = List.map (TypeChecking.type_pred env Local.empty) hyps in
      let () = Closed_Global_Context.set_in_rw env true in
      let (ty_rhs,rhs2) = TypeChecking.type_expr env Local.empty rhs in
      (* --- *)
      match Closed_Global_Context.get_stype env ty_lhs ty_rhs with (* Rq: ty_lhs is closed *)
      | Some _ ->
        (T.Rewrite_E(List.map (to_m_pred env) binhyps,
                     List.map (to_m_pred env) hyps,
                     to_m_expr env lhs2,
                     to_m_expr env rhs2),
        to_typing_env env)
      | None -> TypeChecking.unexpected_type env rhs ty_rhs ty_lhs
    end
  | P.Rewrite_P (guards,hyps,lhs,rhs) ->
    begin
      let (binhyps, bnfree, bfresh, blvar) = read_guards guards in
      (*Step 1: infer*)
      let env = Open_Global_Context.create bnfree blvar in
      let () = Open_Global_Context.set_in_rw env true in
      let lhs = TypeInference.type_pred env Local.empty lhs in
      let () = Open_Global_Context.set_in_rw env false in
      let binhyps = List.map (TypeInference.type_pred env Local.empty) binhyps in
      (*Step 2: check*)
      let env = close env in
      let hyps = List.map (TypeChecking.type_pred env Local.empty) hyps in
      let () = Closed_Global_Context.set_in_rw env true in
      let rhs = TypeChecking.type_pred env Local.empty rhs in
      (* --- *)
      (T.Rewrite_P(List.map (to_m_pred env) binhyps,
                   List.map (to_m_pred env) hyps,
                   to_m_pred env lhs,
                   to_m_pred env rhs),
       to_typing_env env)
    end

(* ************************** REPORT **************************************** *)

let print_report (out:out_channel) (env:typing_env) : unit =
  let aux id = function
    | Global_Context_Common.E (ctx,ty) ->
      Printf.fprintf out "The joker '%s' is an expression of type '%s' in context %a.\n"
        id (Btype.Poly.to_string ty) FV_Context.pp ctx
    | Global_Context_Common.P ctx ->
      Printf.fprintf out "The joker '%s' is a predicate with context %a.\n"
        id FV_Context.pp ctx
  in
  Printf.fprintf out "TYPING CONTEXT:\n";
  M.iter aux env

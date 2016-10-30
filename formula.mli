open Utils
open Syntax

val ignore_unknown_guards : bool ref

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
  | Application
  | Image
  | Substitution
  | Other_Binary
  | Antislash
  | Bar
  | Affectation
  | BinOp_Expr of loc*e_builtin
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

type t_guard =
  | G_Not_Supported
  | G_band
  | G_bforward
  | G_bfresh
  | G_blvar
  | G_binhyp

type r_rule = formula list * t_goal

type r_theory = { tloc:loc; tname:string; trules: r_rule list; }

val get_loc : formula -> loc

exception Error of loc*string

val to_expression : formula -> expression

val to_predicate : formula -> predicate

val to_rule : r_rule -> rule

val to_theory : r_theory -> theory

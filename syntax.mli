open Utils

type inclusion = Not_Strict | Strict | Non_Inclusion | Non_Strict_Inclusion

type inequality = Smaller_or_Equal | Strictly_Smaller | Greater_or_Equal | Strictly_Greater

type prop_bop = Conjonction | Disjonction | Implication | Equivalence

val prop_bop_to_string : prop_bop -> string

type pred_bop = Equality | Disequality | Membership | Non_Membership
             | Inclusion of inclusion | Inequality of inequality

val pred_bop_to_string : pred_bop -> string

type power_set = Full | Non_Empty | Finite | Finite_Non_Empty

type stype = All_Seq | Non_Empty_Seq | Injective_Seq | Injective_Non_Empty_Seq | Permutations

type ftype =
  | Partial_Functions | Total_Functions | Partial_Injections | Total_Injections
  | Partial_Surjections | Total_Surjections | Bijections

type 'a e_builtin =
  | Integer of int | MaxInt | MinInt | Successor | Predecessor | INTEGER
  | NATURAL | NATURAL1 | INT | NAT | NAT1 | STRINGS | BOOLEANS | Product
  | Difference | Addition | Division | Modulo | Power | Interval | Union
  | Intersection | Relations | First_Projection | Second_Projection
  | Composition | Direct_Product | Parallel_Product | Iteration | Image
  | Domain_Restriction | Domain_Soustraction | Codomain_Restriction
  | Codomain_Soustraction | Surcharge | Functions of ftype | Concatenation
  | Head_Insertion | Tail_Insertion | Head_Restriction | Tail_Restriction
  | Cardinal | Power_Set of power_set | Identity_Relation | Inverse_Relation
  | Closure | Transitive_Closure | Domain | Range | Fnc | Rel
  | Sequence_Set of stype | Size | First | Last | Front | Tail | Reverse
  | G_Union | G_Intersection | G_Concatenation | Unary_Minus | Max | Min
  | TRUE | FALSE | Empty_Set of 'a | Empty_Seq of 'a

val builtin_to_string : 'a e_builtin -> string

type expr_binder = Sum | Prod | Q_Union | Q_Intersection | Lambda

val binder_to_string : expr_binder -> string

module P : sig

  type loc = Lexing.position
  val dloc : loc
  type ident = loc*string
  val ident_eq : ident -> ident -> bool

  type c_or_m = Maplet | Comma | Infix

  type p_builtin =
    | Btrue
    | Bfalse

  type expression =
    | Ident of ident
    | Builtin of loc*unit e_builtin
    | Pbool of loc*predicate
    | Parentheses of loc*expression
    | Application of loc*expression*expression
    | Couple of loc*c_or_m*expression*expression
    | Sequence of loc*expression non_empty_list
    | Extension of loc*expression non_empty_list
    | Comprehension of loc*ident non_empty_list * predicate
    | Binder of loc*expr_binder*ident non_empty_list*predicate*expression
    | Substitution of loc*ident*expression*ident

  and predicate =
    | P_Ident of ident
    | P_Builtin of loc*p_builtin
    | Binary_Prop of loc*prop_bop*predicate*predicate
    | Binary_Pred of loc*pred_bop*expression*expression
    | Negation of loc*predicate
    | Pparentheses of loc*predicate
    | Universal_Q of loc*ident non_empty_list*predicate
    | Existential_Q of loc*ident non_empty_list*predicate
    | P_Substitution of loc*ident*expression*ident

  val expr_loc : expression -> loc

  val pp_expr : expression -> unit
  val pp_pred : predicate -> unit

  type guard =
    | Binhyp of loc*predicate
    | Bfresh of loc*ident*ident list
    | Blvar of loc*ident
    | Bnfree of loc*ident list*ident list

  type rule =
    | Backward of guard list * predicate list * predicate
    | Forward of guard list * predicate list * predicate
    | Rewrite_E of guard list * predicate list * expression * expression
    | Rewrite_P of guard list * predicate list * predicate * predicate

  type theory = { tloc:loc; tname:string; trules: rule list; }
end

module T :
sig
  type p_builtin =
    | Btrue
    | Bfalse
    | WellDefProp of string
    | WellDefExpr of string

  type 't expression =
    | FVar of 't*string
    | BVar of string
    | Const of 't*string
    | Builtin of 't e_builtin
    | Pbool of 't predicate
    | Application of 't expression* 't expression
    | Couple of 't expression* 't expression
    | Sequence of ('t expression) non_empty_list
    | Extension of ('t expression) non_empty_list
    | Comprehension of ('t*string) non_empty_list * 't predicate
    | Binder of expr_binder*('t*string) non_empty_list*'t predicate*'t expression

  and 't predicate =
    | PVar of string
    | P_Builtin of p_builtin
    | Binary_Prop of prop_bop*'t predicate*'t predicate
    | Binary_Pred of pred_bop*'t expression*'t expression
    | Negation of 't predicate
    | Universal_Q of string*'t * 't predicate
    | Existential_Q of string*'t * 't predicate

  type p_expression = Btype.Poly.btype expression
  type p_predicate = Btype.Poly.btype predicate
  type m_expression = Btype.Mono.btype expression
  type m_predicate = Btype.Mono.btype predicate

  type rule =
    | Backward  of m_predicate list * m_predicate list * m_predicate
    | Forward   of m_predicate list * m_predicate list * m_predicate
    | Rewrite_E of m_predicate list * m_predicate list * m_expression * m_expression
    | Rewrite_P of m_predicate list * m_predicate list * m_predicate * m_predicate

end

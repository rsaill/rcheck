open Utils

type inclusion = Not_Strict | Strict | Non_Inclusion | Non_Strict_Inclusion

type inequality = Smaller_or_Equal | Strictly_Smaller | Greater_or_Equal | Strictly_Greater

type prop_bop = Conjonction | Disjonction | Implication | Equivalence

type pred_bop = Equality | Disequality | Membership | Non_Membership
             | Inclusion of inclusion | Inequality of inequality

type pred_uop = IsFinite

type power_set = Full | Non_Empty | Finite | Finite_Non_Empty

type stype = All_Seq | Non_Empty_Seq | Injective_Seq | Injective_Non_Empty_Seq | Permutations

type ftype =
  | Partial_Functions | Total_Functions | Partial_Injections | Total_Injections
  | Partial_Surjections | Total_Surjections | Bijections

type e_builtin =
  | Integer of int
  | MaxInt | MinInt | Successor | Predecessor
  | INTEGER | NATURAL | NATURAL1 | INT | NAT | NAT1 | STRINGS | BOOLEANS
  | Empty_Set | Empty_Seq
  | Product | Difference | Addition | Division | Modulo | Power
  | Interval | Union | Intersection | Relations | First_Projection
  | Second_Projection | Composition | Direct_Product | Parallel_Product | Iteration
  | Image | Domain_Restriction | Domain_Soustraction | Codomain_Restriction
  | Codomain_Soustraction | Surcharge | Functions of ftype | Concatenation | Head_Insertion
  | Tail_Insertion | Head_Restriction | Tail_Restriction
  | Cardinal | Power_Set of power_set | Identity_Relation | Inverse_Relation
  | Closure | Transitive_Closure | Domain | Range | Fnc | Rel
  | Sequence_Set of stype | Size | First | Last | Front | Tail | Reverse
  | G_Union | G_Intersection | G_Concatenation | Unary_Minus
  | Max | Min | TRUE | FALSE

type p_builtin =
  | Btrue
  | Bfalse
  | WellDefProp of string
  | WellDefExpr of string

type expr_binder = Sum | Prod | Q_Union | Q_Intersection | Lambda

type c_or_m = Maplet | Comma | Infix

type expression =
  | Ident of ident
  | Builtin of loc*e_builtin
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
  | Unary_Pred of loc*pred_uop*expression
  | Negation of loc*predicate
  | Pparentheses of loc*predicate
  | Universal_Q of loc*ident non_empty_list*predicate
  | Existential_Q of loc*ident non_empty_list*predicate
  | P_Substitution of loc*ident*expression*ident

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

let expr_loc : expression -> loc = function
  | Ident id -> fst id
  | Builtin (l,_) | Pbool (l,_) | Parentheses (l,_) | Application (l,_,_)
  | Couple (l,_,_,_) | Sequence (l,_) | Extension (l,_) | Comprehension (l,_,_)
  | Binder (l,_,_,_,_) | Substitution (l,_,_,_) -> l

(* Print *)

open Format

let ofst = 2

let pred_uop_to_string : pred_uop -> string = function
  | IsFinite -> "IsFinite"

let pred_bop_to_string : pred_bop -> string = function
  | Equality -> "="
  | Disequality -> "\\="
  | Membership -> ":"
  | Non_Membership -> "/:"
  | Inclusion Not_Strict -> "<:"
  | Inclusion Strict -> "<<:"
  | Inclusion Non_Inclusion -> "/<:"
  | Inclusion Non_Strict_Inclusion -> "/<<:"
  | Inequality Smaller_or_Equal -> "<="
  | Inequality Strictly_Smaller -> "<"
  | Inequality Greater_or_Equal -> ">="
  | Inequality Strictly_Greater -> ">"

let prop_bop_to_string : prop_bop -> string = function
  | Conjonction -> "&"
  | Disjonction -> "or"
  | Implication -> "=>"
  | Equivalence -> "<=>"

let builtin_to_string : e_builtin -> string = function
  | Integer i -> string_of_int i
  | TRUE -> "TRUE"
  | FALSE -> "FALSE"
  | MaxInt -> "MaxInt"
  | MinInt -> "MinInt"
  | INTEGER -> "INTEGER"
  | NATURAL -> "NATURAL"
  | NATURAL1 -> "NATURAL1"
  | INT -> "INT"
  | NAT -> "NAT"
  | NAT1 -> "NAT1"
  | STRINGS -> "STRING"
  | BOOLEANS -> "BOOLEAN"
  | Empty_Set -> "[]"
  | Empty_Seq -> "{}"
  | Successor -> "Succ"
  | Predecessor -> "Pred"
  | Cardinal -> "card"
  | Power_Set Full -> "POW"
  | Power_Set Non_Empty -> "POW1"
  | Power_Set Finite -> "FIN"
  | Power_Set Finite_Non_Empty -> "FIN1"
  | Identity_Relation -> "id"
  | Closure -> "closure"
  | Transitive_Closure -> "closure1"
  | Domain -> "dom"
  | Range -> "ran"
  | Fnc -> "fnc"
  | Rel -> "rel"
  | Sequence_Set All_Seq -> "seq"
  | Sequence_Set Non_Empty_Seq -> "seq1"
  | Sequence_Set Injective_Seq -> "iseq"
  | Sequence_Set Injective_Non_Empty_Seq -> "iseq1"
  | Sequence_Set Permutations -> "perm"
  | Size -> "size"
  | First -> "first"
  | Last -> "last"
  | Front -> "front"
  | Tail -> "tail"
  | Reverse -> "rev"
  | G_Union -> "union"
  | G_Intersection -> "inter"
  | G_Concatenation -> "conc"
  | Max -> "max"
  | Min -> "min"
  | First_Projection -> "prj1"
  | Second_Projection -> "prj2"
  | Iteration -> "iterate"

  | Image -> "image"
  | Unary_Minus -> "unary_minus"
  | Inverse_Relation -> "inverse"

  | Product -> "*"
  | Difference -> "-"
  | Addition -> "+"
  | Division -> "/"
  | Modulo -> "mod"
  | Power -> "**"
  | Interval -> ".."
  | Union -> "\\/"
  | Intersection -> "/\\"
  | Relations -> "<->"
  | Composition -> ";"
  | Direct_Product -> "><"
  | Parallel_Product -> "||"
  | Domain_Restriction -> "<|"
  | Domain_Soustraction -> "<<|"
  | Codomain_Restriction -> "|>"
  | Codomain_Soustraction -> "|>>"
  | Surcharge -> "<+"
  | Functions Partial_Functions -> "+->"
  | Functions Partial_Injections -> ">+->"
  | Functions Total_Injections -> ">->"
  | Functions Total_Functions -> "-->"
  | Functions Total_Surjections -> "-->>"
  | Functions Partial_Surjections -> "+->>"
  | Functions Bijections -> ">->>"
  | Concatenation -> "^"
  | Head_Insertion -> "->"
  | Tail_Insertion -> "<-"
  | Head_Restriction -> "/|\\"
  | Tail_Restriction -> "\\|/"

let binder_to_string = function
  | Sum -> "SIGMA"
  | Prod -> "PI"
  | Q_Union -> "UNION"
  | Q_Intersection -> "INTER"
  | Lambda -> "%"

let rec pp_expr : expression -> unit = function
  | Ident id -> print_string (snd id)
  | Builtin (_,bi) -> print_string (builtin_to_string bi)
  | Pbool (_,p) ->
    begin
      open_box ofst;
      print_string "pbool(";
      pp_pred p;
      print_string ")";
      close_box ();
    end
  | Parentheses (_,e) ->
    begin
      open_box ofst;
      print_string "(";
      pp_expr e;
      print_string ")";
      close_box ();
    end
  | Application (_,Builtin (_,Inverse_Relation),e) ->
    begin
      open_box ofst;
      pp_expr_wp e;
      print_string "~";
      close_box ();
    end
  | Application (_,Builtin (_,Unary_Minus),e) ->
    begin
      open_box ofst;
      print_string "-";
      pp_expr_wp e;
      close_box ();
    end
  | Application (_,Builtin (_,Image),Couple(_,_,e1,e2)) ->
    begin
      open_box ofst;
      pp_expr_wp e1;
      print_string "[";
      pp_expr e2;
      print_string "]";
      close_box ();
    end
  | Application (_,Builtin (_,bop),Couple(_,Infix,e1,e2)) ->
    begin
      open_box ofst;
      pp_expr_wp e1;
      print_space ();
      print_string (builtin_to_string bop);
      print_space ();
      pp_expr_wp e2;
      close_box ();
    end
  | Application (_,f,a) ->
    begin
        open_box ofst;
        pp_expr_wp f;
        print_string "(";
        pp_expr a;
        print_string ")";
        close_box ();
      end
  | Comprehension (l,(e,lst),p) ->
    begin
      open_box ofst;
      print_string "{";
      print_string (snd e);
      List.iter (fun e -> print_string ", "; print_string (snd e)) lst;
      print_string " |";
      print_space ();
      pp_pred p;
      print_string "}";
      close_box ();
    end
  | Binder (l,bi,(x,lst),p,e) ->
    begin
      open_box ofst;
      print_string (binder_to_string bi ^ "(");
      print_string (snd x);
      List.iter (fun (_,x) -> print_string (","^x)) lst;
      print_string ").(";
      print_space ();
      pp_pred p;
      print_string " |";
      print_space ();
      pp_expr e;
      print_string ")";
      close_box ();
    end
  | Sequence (_,(e,lst)) ->
    begin
      open_box ofst;
      print_string "[";
      pp_expr e;
      List.iter (fun e -> print_string ","; print_space (); pp_expr e) lst;
      print_string "]";
      close_box ();
    end
  | Extension (_,(e,lst)) ->
    begin
      open_box ofst;
      print_string "{";
      pp_expr e;
      List.iter (fun e -> print_string ","; print_space (); pp_expr e) lst;
      print_string "}";
      close_box ();
    end
  | Couple (_,ki,e1,e2) ->
    begin
      open_box ofst;
      pp_expr_wp e1;
      ( match ki with
        | Comma -> ( print_string ","; print_space () )
        | Maplet -> ( print_space (); print_string "|->"; print_space () )
        | Infix -> assert false );
      pp_expr_wp e2;
      close_box ();
    end
  | Substitution _ -> failwith "not implemented: substitution."

and pp_expr_wp : expression -> unit = function
  | Ident _ | Pbool _ | Builtin _ | Parentheses _ | Comprehension _ | Binder _
  | Sequence _ | Extension _ as e -> pp_expr e
  | Application (_,_,Couple(_,Infix,_,_)) | Couple _ as e ->
    begin
      open_box ofst;
      print_string "(";
      pp_expr e;
      print_string ")";
      close_box ();
    end
  | Application _ as e -> pp_expr e
  | Substitution _ -> failwith "not implemented: substitution."

and pp_pred : predicate -> unit = function
  | P_Ident id -> print_string (snd id)
  | P_Builtin (_,Btrue) -> print_string "True"
  | P_Builtin (_,Bfalse) -> print_string "False"
  | P_Builtin (_,WellDefProp id) -> print_string ("Delta_p("^id^")")
  | P_Builtin (_,WellDefExpr id) -> print_string ("Delta_e("^id^")")
  | Binary_Prop (_,bop,p1,p2) ->
    begin
      open_box ofst;
      pp_pred_wp p1;
      print_space ();
      print_string (prop_bop_to_string bop);
      print_space ();
      pp_pred_wp p2;
      close_box ();
    end
  | Binary_Pred (_,bop,e1,e2) ->
    begin
      open_box ofst;
      pp_expr e1;
      print_space ();
      print_string (pred_bop_to_string bop);
      print_space ();
      pp_expr e2;
      close_box ();
    end
  | Unary_Pred (_,uop,e) ->
    begin
      open_box ofst;
      print_string (pred_uop_to_string uop ^ "(");
      pp_expr e;
      print_string ")";
      close_box ();
    end
  | Negation (_,p) ->
    begin
      open_box ofst;
      print_string "not(";
      pp_pred p;
      print_string ")";
      close_box ();
    end
  | Pparentheses (_,p) ->
    begin
      open_box ofst;
      print_string "(";
      pp_pred p;
      print_string ")";
      close_box ();
    end
  | Universal_Q (_,(x,lst),p) ->
    begin
      open_box ofst;
      print_string "!(";
      print_string (snd x);
      List.iter (fun (_,x) -> print_string (","^x)) lst;
      print_string ").(";
      print_space ();
      pp_pred p;
      print_space ();
      print_string ")";
      close_box ();
    end
  | Existential_Q (_,(x,lst),p) ->
    begin
      open_box ofst;
      print_string "#(";
      print_string (snd x);
      List.iter (fun (_,x) -> print_string (","^x)) lst;
      print_string ").(";
      print_space ();
      pp_pred p;
      print_space ();
      print_string ")";
      close_box ();
    end
  | P_Substitution _ -> failwith "not implemented: substitution."

and pp_pred_wp : predicate -> unit = function
  | P_Ident _ | P_Builtin _ | Unary_Pred _
  | Negation _ | Pparentheses _ | Universal_Q _ | Existential_Q _ as p -> pp_pred p
  | Binary_Prop _ | Binary_Pred _ as p ->
    begin
      open_box ofst;
      print_string "(";
      pp_pred p;
      print_string ")";
      close_box ();
    end
  | P_Substitution _ -> failwith "not implemented: substitution."

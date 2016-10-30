type btype =
  | T_INTEGER
  | T_BOOL
  | T_STRING
  | T_Set of string
  | T_Power of btype
  | T_Product of btype * btype
  | T_Meta of int

let type_of_func (t_arg:btype) (t_res:btype) : btype =
  T_Power (T_Product(t_arg,t_res))

let type_of_func2 (t_arg1:btype) (t_arg2:btype) (t_res:btype) : btype =
  T_Power (T_Product(T_Product (t_arg1,t_arg2),t_res))

let type_of_seq (ty:btype) : btype =
  type_of_func T_INTEGER ty

let rec to_string_np () = function
  | T_INTEGER -> "INTEGER"
  | T_BOOL -> "BOOL"
  | T_STRING -> "STRING"
  | T_Set s -> s
  | T_Power t -> Printf.sprintf "POW(%a)" to_string_np t
  | T_Product (t1,t2) -> Printf.sprintf "%a*%a" to_string_wp t1 to_string_wp t2
  | T_Meta i -> "?" ^ string_of_int i
and to_string_wp () = function
  | (T_Product _) as t -> Printf.sprintf "( %a )" to_string_np t
  | t ->  to_string_np () t

let to_string = to_string_np ()
  let rec occurs (n:int) : btype -> bool = function
  | T_INTEGER
  | T_BOOL
  | T_STRING
  | T_Set _ -> false
  | T_Power ty -> occurs n ty
  | T_Product (ty1,ty2) -> ( occurs n ty1 || occurs n ty2 )
  | T_Meta m -> n=m

  let rec subst (n:int) (rep:btype) : btype -> btype = function
    | ( T_INTEGER | T_BOOL | T_STRING | T_Set _ ) as ty -> ty
    | T_Power ty -> T_Power (subst n rep ty)
    | T_Product (ty1,ty2) -> T_Product (subst n rep ty1,subst n rep ty2)
    | T_Meta m as ty -> if n=m then rep else ty

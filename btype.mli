module Poly : sig

  type btype =
    | T_INTEGER
    | T_BOOL
    | T_STRING
    | T_Set of string
    | T_Power of btype
    | T_Product of btype * btype
    | T_Meta of int

  val type_of_func : btype -> btype -> btype 
  val type_of_func2 : btype -> btype -> btype -> btype 
  val type_of_seq : btype -> btype 
  val close : btype -> btype

  val to_string : btype -> string
  val occurs : int -> btype -> bool
  val subst : int -> btype -> btype -> btype

end

module Mono : sig

  type btype =
    | T_INTEGER
    | T_BOOL
    | T_STRING
    | T_Set of string
    | T_Power of btype
    | T_Product of btype * btype

  val close : Poly.btype -> btype
end

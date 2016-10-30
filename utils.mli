type ('a,'b) union = Success of 'a | Failure of 'b

val bind: ('a,'e) union -> ('a -> ('c,'e) union) -> ('c,'e) union
val (>>=): ('a,'e) union -> ('a -> ('c,'e) union) -> ('c,'e) union

type loc = Lexing.position
val dloc : loc
type ident = loc*string
val ident_eq : ident -> ident -> bool

type 'a t_error = ('a,loc*string) union
type 'a non_empty_list = 'a*'a list

type ('a,'b) union = Success of 'a | Failure of 'b

val bind: ('a,'e) union -> ('a -> ('c,'e) union) -> ('c,'e) union
val (>>=): ('a,'e) union -> ('a -> ('c,'e) union) -> ('c,'e) union

type 'a t_error = ('a,Lexing.position*string) union
type 'a non_empty_list = 'a*'a list

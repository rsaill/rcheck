type ('a,'b) union = Success of 'a | Failure of 'b

let bind u f =
  match u with
  | Success a -> f a
  | Failure a -> Failure a

let (>>=) = bind

type 'a t_error = ('a,Lexing.position*string) union
type loc = Lexing.position
let dloc = Lexing.dummy_pos
type ident = loc*string
type 'a non_empty_list = 'a*'a list

let ident_eq (_,s1) (_,s2) = ( String.compare s1 s2 = 0 )

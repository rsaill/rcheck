type ('a,'b) union = Success of 'a | Failure of 'b

let bind u f =
  match u with
  | Success a -> f a
  | Failure a -> Failure a

let (>>=) = bind

type 'a t_error = ('a,Lexing.position*string) union
type 'a non_empty_list = 'a*'a list

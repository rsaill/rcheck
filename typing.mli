open Syntax

exception Error of P.loc*string

type typing_env
val check_rule : P.rule -> T.rule*typing_env 
val print_report : out_channel -> typing_env -> unit

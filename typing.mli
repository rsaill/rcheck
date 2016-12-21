
exception Error of Syntax.P.loc*string

type typing_env
val check_rule : Syntax.P.rule -> typing_env
val print_report : typing_env -> unit

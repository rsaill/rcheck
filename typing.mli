
exception Error of Utils.loc*string

type typing_env
val check_rule : Syntax.rule -> typing_env
val print_report : typing_env -> unit

type state
type t_token = Parser.token * Lexing.position * Lexing.position
val get_next : state -> t_token
val mk_state : string -> in_channel -> state
val get_current_pos : state -> Lexing.position
val get_last_token_str : state -> string

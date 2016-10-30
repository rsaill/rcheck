open Lexing

let debug_mode = ref false

let print loc fmt =
  Printf.fprintf stdout "[file:%s;line:%i;column:%i] "
    loc.pos_fname loc.pos_lnum (loc.pos_cnum-loc.pos_bol+1);
  Printf.kfprintf (fun _ -> print_newline () (*; exit 1*) ) stdout fmt

let debug fmt =
  if !debug_mode then Printf.kfprintf (fun _ -> print_newline ()) stdout fmt
  else Printf.ifprintf stdout fmt

let warning loc fmt =
  Printf.fprintf stdout "[file:%s;line:%i;column:%i] "
    loc.pos_fname loc.pos_lnum (loc.pos_cnum-loc.pos_bol+1);
  Printf.kfprintf (fun _ -> print_newline () ) stdout fmt

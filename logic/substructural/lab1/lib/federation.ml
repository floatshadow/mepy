(** Federation: a list of states (collections of possible worlds) *)
open Core

type states = State.state list

let ground states = List.for_all states ~f:State.ground
let sort states = Sort.SortSet.sort Term.compare_list states
let merge s1 s2 = Sort.SortSet.merge Term.compare_list s1 s2
let pp_state ss = String.concat ~sep:", " (List.map ~f:Term.pp_term ss)
let pp_states states = String.concat ~sep:";\n" (List.map ~f:pp_state states)

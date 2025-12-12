(** Federation: a list of states (collections of possible worlds) *)

type states = State.state list

let ground states = List.for_all State.ground states
let sort states = Sort.SortSet.sort Term.compare_list states
let merge s1 s2 = Sort.SortSet.merge Term.compare_list s1 s2
let pp_state ss = String.concat ", " (List.map Term.pp_term ss)
let pp_states states = String.concat ";\n" (List.map pp_state states)

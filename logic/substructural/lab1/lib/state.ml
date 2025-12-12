(** State: a list of ground terms *)

type state = Term.term list

let ground state = List.for_all Term.ground state
let pp_facts ss = String.concat ",\n" (List.map Term.pp_term ss)
let pp_state state = "%-----\n" ^ pp_facts state ^ "\n%-----\n"
let sort_set state = Sort.SortSet.sort Term.compare state
let merge_set s1 s2 = Sort.SortSet.merge Term.compare s1 s2
let sort_multiset state = Sort.SortMultiset.sort Term.compare state
let merge_multiset s1 s2 = Sort.SortMultiset.merge Term.compare s1 s2

signature STATE =
sig

    type state = Term.term list  (* all ground *)

    val ground : state -> bool  (* all propositions in the state must be ground *)

    val sort_set : state -> state
    val merge_set : state -> state -> state

    val sort_multiset : state -> state
    val merge_multiset : state -> state -> state

    val pp_state : state -> string

end  (* signature STATE *)

structure State :> STATE =
struct

structure T = Term

type state = T.term list       (* all ground *)

fun ground state = List.all T.ground state

fun pp_facts ss = String.concatWith ",\n" (List.map T.pp_term ss)

fun pp_state state = "%-----\n" ^ pp_facts state ^ "\n" ^ "%-----\n"

fun sort_set state = SortSet.sort T.compare state (* remove duplicates *)
fun merge_set state1 state2 = SortSet.merge T.compare state1 state2

fun sort_multiset state = SortMultiset.sort T.compare state
fun merge_multiset state1 state2 = SortMultiset.merge T.compare state1 state2

end (* structure State *)


signature FEDERATION =
sig

    type states = State.state list

    val ground : states -> bool
                  
    val sort : states -> states
    val merge : states -> states -> states (* removes duplicates *)
    val pp_state : State.state -> string         (* compact printing *)
    val pp_states : states -> string

end  (* signature FEDERATION *)

structure Federation :> FEDERATION =
struct

structure T = Term
structure S = State

type states = S.state list (* all ground *)

fun ground states = List.all S.ground states

fun sort states = SortSet.sort T.compare_list states
fun merge states1 states2 = SortSet.merge T.compare_list states1 states2

fun pp_state ss = String.concatWith ", " (List.map T.pp_term ss)

fun pp_states states =
    String.concatWith ";\n" (List.map pp_state states)


end  (* structure Federation *)

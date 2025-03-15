signature LINEAR =
sig

    val iterate : Term.rule list -> Federation.states -> Federation.states
    val quiesce : Term.rule list -> State.state -> State.state

    (* for debugging *)
    (* requires rule to be range restricted and state to be ground and sorted *)
    val apply_rule : Term.rule -> State.state -> Federation.states
    
end

structure Linear :> LINEAR =
struct

fun match_premise theta P Delta (Q::Delta') =
    (case Term.match theta P Q
      of NONE => match_premise theta P (Delta @ [Q]) Delta'
       | SOME(theta') => [(theta', Delta @ Delta')] (* consume Q *)
                         @ match_premise theta P (Delta @ [Q]) Delta')
  | match_premise theta P Delta nil = []

fun match_premises theta (P::Ps) Delta =
    let
        val mstates1 = match_premise theta P nil Delta
        val mstates2 = List.concat (List.map (fn (theta', Delta') => match_premises theta' Ps Delta') mstates1)
    in
        mstates2
    end
  | match_premises theta nil Delta = [(theta,Delta)]

fun apply_rule (Term.Rule(Ps, Cs)) state =
    let val mstates = match_premises Term.empty Ps state
        val states' = List.map (fn (theta',Delta') =>
                                   State.merge_multiset (State.sort_multiset (List.map (Term.subst theta') Cs)) Delta')
                               mstates
        val states'' = Federation.sort states'
    in states'' end

fun apply_rules (rule::rules) state =
    Federation.merge (apply_rule rule state)
            (apply_rules rules state)
  | apply_rules nil state = nil

fun apply_rules_states rules (state::states) =
    Federation.merge (apply_rules rules state)
             (apply_rules_states rules states)
  | apply_rules_states rules nil = nil

fun iterate_rec rules states =
    let
        val states1 = apply_rules_states rules states
        val states2 = Federation.merge states1 states
        val changed = List.length states2 > List.length states
    in
        if changed then iterate_rec rules states2 else states2
    end

fun iterate rules states =
    let
        val () = if List.all Term.range_restricted rules then ()
                 else raise Fail "rules not range restricted"
        val () = if Federation.ground states then ()
                 else raise Fail "set of states not ground"
        val states1 = List.map State.sort_multiset states
        val states2 = Federation.sort states1
    in
        iterate_rec rules states2
    end

fun quiesce_rec rules state =
    (case apply_rules rules state
      of nil => state
       | state'::states => quiesce_rec rules state') (* could pick any! *)

fun quiesce rules state =
    let
        val () = if List.all Term.range_restricted rules then ()
                 else raise Fail "rules not range restricted"
        val () = if State.ground state then ()
                 else raise Fail "state not ground"
    in
        quiesce_rec rules state
    end 


end (* structure Linear *)

signature ORDERED =
sig

    val iterate : Term.rule list -> Federation.states -> Federation.states
    val quiesce : Term.rule list -> State.state -> State.state

    (* for debugging *)
    (* require rules to be range restricted and state to be ground *)
    val apply_rule : Term.rule -> State.state -> Federation.states

end

structure Ordered :> ORDERED =
struct

(* a state here is not ordered, according to the term ordering *)
(* a collection of states is ordered *)

fun match_here theta (P::Ps) OmegaL (Q::OmegaR) =
    (case Term.match theta P Q
      of NONE => []
       | SOME(theta') => match_here theta' Ps OmegaL OmegaR)
  | match_here theta (P::Ps) OmegaL nil = []
  | match_here theta nil OmegaL OmegaR = [(OmegaL, theta, OmegaR)]

fun match_premises Ps OmegaL (Q::OmegaR) =
    match_here Term.empty Ps OmegaL (Q::OmegaR)
    @ match_premises Ps (OmegaL @ [Q]) OmegaR
  | match_premises (P::Ps) OmegaL nil = []
  | match_premises nil OmegaL nil = [(OmegaL, Term.empty, [])]

(* premises must be adjacent *)
fun apply_rule (Term.Rule(Ps, Cs)) state =
    let
        val mstates = match_premises Ps nil state
        val states' = List.map (fn (OmegaL, theta', OmegaR) => OmegaL @ List.map (Term.subst theta') Cs @ OmegaR)
                               mstates
        val states'' = Federation.sort states'
    in
        states''
    end

fun apply_rules (rule::rules) state =
    let
        val states1 = apply_rule rule state
        val states2 = apply_rules rules state
    in
        Federation.merge states1 states2 
    end
  | apply_rules nil state = nil

fun apply_rules_states rules (state::states) =
    let
        val states1 = apply_rules rules state
        val states2 = apply_rules_states rules states
    in
        Federation.merge states1 states2
    end
  | apply_rules_states rule nil = nil

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
        val states_sorted = Federation.sort states
    in
        iterate_rec rules states
    end

fun quiesce_rec rules state =
    (case apply_rules rules state
      of nil => state                                (* quiescence *)
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

end (* structure Ordered *)

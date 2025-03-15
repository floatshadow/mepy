signature SATURATE =
sig

    val saturate : Term.rule list -> State.state -> State.state

    (* for debugging *)
    (* requires rules to be range restricted and state to be sorted without duplicates *)
    val apply_rule : Term.rule -> State.state -> State.state

end

structure Saturate :> SATURATE =
struct

fun match_pat theta P nil = []
  | match_pat theta P (Q::Gamma) =
    (case Term.match theta P Q
      of NONE => match_pat theta P Gamma
       | SOME(theta') => theta'::match_pat theta P Gamma)

fun match_pats theta (P::Ps) Gamma =
    List.concat (List.map (fn theta' => match_pats theta' Ps Gamma)
                          (match_pat theta P Gamma))
  | match_pats theta nil Gamma = [theta]

fun apply_merge (theta::thetas) Cs Gamma =
    let
        val thetaCs = State.sort_set (List.map (Term.subst theta) Cs)
        val Gamma' = State.merge_set thetaCs Gamma
    in
        apply_merge thetas Cs Gamma'
    end
  | apply_merge nil Cs Gamma = Gamma

fun apply_rule (Term.Rule(Ps, Cs)) Gamma =
    let
        val thetas = match_pats Term.empty Ps Gamma
    in
        apply_merge thetas Cs Gamma
    end

fun apply_all_rules (rule::rules) Gamma =
    State.merge_set (apply_rule rule Gamma) (apply_all_rules rules Gamma)
  | apply_all_rules nil Gamma = Gamma

(* naive saturation, not semi-naive *)
fun naive rules Gamma =
    let val Gamma' = apply_all_rules rules Gamma
        val changed = (List.length Gamma' > List.length Gamma)
    in if changed then naive rules Gamma' else Gamma' end

fun saturate rules Gamma =
    let
        val () = if List.all Term.range_restricted rules then ()
                 else raise Fail "rules not range restricted"
        val () = if State.ground Gamma then ()
                 else raise Fail "state not ground"
    in
        naive rules (State.sort_set Gamma)
    end

end


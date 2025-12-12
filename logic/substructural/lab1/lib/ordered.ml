(** Ordered logic: premises must be adjacent *)

let rec match_here theta ps omega_l omega_r =
  match ps, omega_r with
  | [], _ -> [ omega_l, theta, omega_r ]
  | _ :: _, [] -> []
  | p :: ps', q :: omega_r' ->
    (match Term.match_ theta p q with
     | None -> []
     | Some theta' -> match_here theta' ps' omega_l omega_r')
;;

let rec match_premises ps omega_l omega_r =
  match ps, omega_r with
  | _ :: _, [] -> []
  | [], [] -> [ omega_l, Term.empty, [] ]
  | _, q :: omega_r' ->
    match_here Term.empty ps omega_l omega_r
    @ match_premises ps (omega_l @ [ q ]) omega_r'
;;

let apply_rule (Term.Rule (ps, cs)) state =
  let mstates = match_premises ps [] state in
  let states' =
    List.map
      (fun (omega_l, theta', omega_r) ->
         omega_l @ List.map (Term.subst theta') cs @ omega_r)
      mstates
  in
  Federation.sort states'
;;

let rec apply_rules rules state =
  match rules with
  | [] -> []
  | rule :: rules' ->
    let states1 = apply_rule rule state in
    let states2 = apply_rules rules' state in
    Federation.merge states1 states2
;;

let rec apply_rules_states rules states =
  match states with
  | [] -> []
  | state :: states' ->
    let states1 = apply_rules rules state in
    let states2 = apply_rules_states rules states' in
    Federation.merge states1 states2
;;

let rec iterate_rec rules states =
  let states1 = apply_rules_states rules states in
  let states2 = Federation.merge states1 states in
  let changed = List.length states2 > List.length states in
  if changed then iterate_rec rules states2 else states2
;;

let iterate rules states =
  if not (List.for_all Term.range_restricted rules)
  then failwith "rules not range restricted";
  if not (Federation.ground states) then failwith "set of states not ground";
  let _states_sorted = Federation.sort states in
  iterate_rec rules states
;;

let rec quiesce_rec rules state =
  match apply_rules rules state with
  | [] -> state (* quiescence *)
  | state' :: _ -> quiesce_rec rules state' (* could pick any *)
;;

let quiesce rules state =
  if not (List.for_all Term.range_restricted rules)
  then failwith "rules not range restricted";
  if not (State.ground state) then failwith "state not ground";
  quiesce_rec rules state
;;

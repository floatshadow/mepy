(** Linear logic: resources are consumed *)
open Core

let rec match_premise theta p delta delta' =
  match delta' with
  | [] -> []
  | q :: delta'' ->
    (match Term.match_term theta p q with
     | None -> match_premise theta p (delta @ [ q ]) delta''
     | Some theta' ->
       (* consume q *)
       (theta', delta @ delta'') :: match_premise theta p (delta @ [ q ]) delta'')
;;

let rec match_premises theta ps delta =
  match ps with
  | [] -> [ theta, delta ]
  | p :: ps' ->
    let mstates1 = match_premise theta p [] delta in
    List.concat_map mstates1 ~f:(fun (theta', delta') -> match_premises theta' ps' delta')
;;

let apply_rule (Term.Rule (ps, cs)) state =
  let mstates = match_premises Term.empty ps state in
  let states' =
    List.map mstates ~f:(fun (theta', delta') ->
      State.merge_multiset
        (State.sort_multiset (List.map cs ~f:(Term.subst theta')))
        delta')
  in
  Federation.sort states'
;;

let rec apply_rules rules state =
  match rules with
  | [] -> []
  | rule :: rules' -> Federation.merge (apply_rule rule state) (apply_rules rules' state)
;;

let rec apply_rules_states rules states =
  match states with
  | [] -> []
  | state :: states' ->
    Federation.merge (apply_rules rules state) (apply_rules_states rules states')
;;

let rec iterate_rec rules states =
  let states1 = apply_rules_states rules states in
  let states2 = Federation.merge states1 states in
  let changed = List.length states2 > List.length states in
  if changed then iterate_rec rules states2 else states2
;;

let iterate rules states =
  if not (List.for_all rules ~f:Term.range_restricted)
  then failwith "rules not range restricted";
  if not (Federation.ground states) then failwith "set of states not ground";
  let states1 = List.map states ~f:State.sort_multiset in
  let states2 = Federation.sort states1 in
  iterate_rec rules states2
;;

let rec quiesce_rec rules state =
  match apply_rules rules state with
  | [] -> state
  | state' :: _ -> quiesce_rec rules state' (* could pick any *)
;;

let quiesce rules state =
  if not (List.for_all rules ~f:Term.range_restricted)
  then failwith "rules not range restricted";
  if not (State.ground state) then failwith "state not ground";
  quiesce_rec rules state
;;

(** Saturation for persistent (classical) logic *)
open Core

let match_pat theta p gamma =
  List.filter_map gamma ~f:(fun q -> Term.match_term theta p q)
;;

let rec match_pats theta ps gamma =
  match ps with
  | [] -> [ theta ]
  | p :: ps' ->
    let thetas = match_pat theta p gamma in
    List.concat_map thetas ~f:(fun theta' -> match_pats theta' ps' gamma)
;;

let rec apply_merge thetas cs gamma =
  match thetas with
  | [] -> gamma
  | theta :: thetas' ->
    let theta_cs = State.sort_set (List.map cs ~f:(Term.subst theta)) in
    let gamma' = State.merge_set theta_cs gamma in
    apply_merge thetas' cs gamma'
;;

let apply_rule (Term.Rule (ps, cs)) gamma =
  let thetas = match_pats Term.empty ps gamma in
  apply_merge thetas cs gamma
;;

let rec apply_all_rules rules gamma =
  match rules with
  | [] -> gamma
  | rule :: rules' ->
    State.merge_set (apply_rule rule gamma) (apply_all_rules rules' gamma)
;;

(** Naive saturation (not semi-naive) *)
let rec naive rules gamma =
  let gamma' = apply_all_rules rules gamma in
  let changed = List.length gamma' > List.length gamma in
  if changed then naive rules gamma' else gamma'
;;

let saturate rules gamma =
  if not (List.for_all rules ~f:Term.range_restricted)
  then failwith "rules not range restricted";
  if not (State.ground gamma) then failwith "state not ground";
  naive rules (State.sort_set gamma)
;;

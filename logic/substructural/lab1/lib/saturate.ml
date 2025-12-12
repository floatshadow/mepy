(** Saturation for persistent (classical) logic *)

let match_pat theta p gamma = List.filter_map (fun q -> Term.match_ theta p q) gamma

let rec match_pats theta ps gamma =
  match ps with
  | [] -> [ theta ]
  | p :: ps' ->
    let thetas = match_pat theta p gamma in
    List.concat_map (fun theta' -> match_pats theta' ps' gamma) thetas
;;

let rec apply_merge thetas cs gamma =
  match thetas with
  | [] -> gamma
  | theta :: thetas' ->
    let theta_cs = State.sort_set (List.map (Term.subst theta) cs) in
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
  if not (List.for_all Term.range_restricted rules)
  then failwith "rules not range restricted";
  if not (State.ground gamma) then failwith "state not ground";
  naive rules (State.sort_set gamma)
;;

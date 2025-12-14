(** Terms, substitutions, and inference rules *)
open Core

type var = string
type const = string

type term =
  | Con of const * term list
  | Var of var

let rec ground = function
  | Con (_, ts) -> List.for_all ~f:ground ts
  | Var _ -> false
;;

let rec pp_term = function
  | Con (a, []) -> a
  | Con (f, ts) -> f ^ "(" ^ pp_terms ts ^ ")"
  | Var x -> x

and pp_terms = function
  | [ t ] -> pp_term t
  | t :: ts -> pp_term t ^ "," ^ pp_terms ts
  | [] -> ""
;;

(** compare t s = Lt | Eq | Gt, requires t, s ground *)
let rec compare t1 t2 =
  match t1, t2 with
  | Con (f, ts), Con (g, ss) ->
    (match Sort.order_of_int (String.compare f g) with
     | Sort.Lt -> Sort.Lt
     | Sort.Eq -> compare_list ts ss
     | Sort.Gt -> Sort.Gt)
  | _ -> failwith "compare: non-ground term"

and compare_list ts ss =
  match ts, ss with
  | t :: ts', s :: ss' ->
    (match compare t s with
     | Sort.Lt -> Sort.Lt
     | Sort.Eq -> compare_list ts' ss'
     | Sort.Gt -> Sort.Gt)
  | [], _ :: _ -> Sort.Lt
  | _ :: _, [] -> Sort.Gt
  | [], [] -> Sort.Eq
;;

(** Substitutions: theta = [(x1,t1); ...; (xn,tn)] with xi distinct, ti ground *)
type subst = (var * term) list

let empty : subst = []

let rec subst theta t =
  match t with
  | Con (f, ts) -> Con (f, List.map ~f:(subst theta) ts)
  | Var y ->
    (match List.Assoc.find theta y ~equal:String.equal with
     | Some t' -> t'
     | None -> failwith ("undefined variable " ^ y))
;;

let subst_var theta y = List.Assoc.find theta y ~equal:String.equal

(** match theta t s = Some theta' extending theta with subst theta' t = s
    requires s ground *)
let rec match_term (theta : subst) t s =
  assert (ground s);
  match t, s with
  | Var x, (Con _ as s') ->
    (match subst_var theta x with
     | Some t' -> match_term theta t' s'
     | None -> Some ((x, s') :: theta))
  | Con (f, ts), Con (g, ss) ->
    if String.(f = g) then match_term_list theta ts ss else None
  | _ -> None

and match_term_list (theta : subst) ts ss =
  match ts, ss with
  | [], [] -> Some theta
  | t :: ts', s :: ss' ->
    (match match_term theta t s with
     | Some theta' -> match_term_list theta' ts' ss'
     | None -> None)
  | _ -> None
;;

(** Rules of inference: Rule(premises, conclusions) *)
type rule = Rule of term list * term list

let rec occurs_in t x =
  match t with
  | Var y -> String.(x = y)
  | Con (_, ts) -> occurs_in_list ts x

and occurs_in_list ts x = List.exists ~f:(fun t -> occurs_in t x) ts

let rec rr premises t =
  match t with
  | Var x -> occurs_in_list premises x
  | Con (_, ss) -> List.for_all ~f:(rr premises) ss
;;

(** range_restricted (Rule(premises, conclusions)) = true
    iff every variable in conclusions occurs in at least one premise *)
let range_restricted (Rule (premises, conclusions)) =
  List.for_all ~f:(rr premises) conclusions
;;

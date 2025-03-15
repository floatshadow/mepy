signature TERM =
sig

    type var = string
    type const = string
    datatype term = Con of const * term list
                  | Var of var

    val ground : term -> bool (* contains no variables *)

    val pp_term : term -> string

    (* compare s t = LESS | EQUAL | GREATER
     * requires s, t ground
     *)
    val compare : term -> term -> order
    val compare_list : term list -> term list -> order

    (* theta = (t1/x1,...,tn/xn); xi distinct, ti ground *)
    type subst = (var * term) list
    val empty : subst
    val subst : subst -> term -> term      (* subst theta t = theta(t), theta(t) ground *)

    (* match theta t s = SOME(theta') for theta' >= theta with subst theta' t = s
     * match theta t s = NONE if no such theta' exists
     * requires s ground; t may contain variables
     *)
    val match : subst -> term -> term -> subst option

    (* Rule(premises, conclusions) *)
    datatype rule = Rule of term list * term list

    (* range_restricted (Rule(premises, conclusions))
     * iff every variable in conclusions occurs in at least one premise
     *)
    val range_restricted : rule -> bool

end  (* signature TERM *)


structure Term :> TERM =
struct
    
type var = string
type const = string
             
datatype term = Con of const * term list
              | Var of var

fun ground (Con(a,ts)) = ground_list ts
  | ground (Var _) = false
and ground_list ts = List.all ground ts

fun pp_term (Con(a,[])) = a
  | pp_term (Con(f,ts)) = f ^ "(" ^ pp_terms ts ^ ")"
  | pp_term (Var(x)) = x
and pp_terms (t::nil) = pp_term t
  | pp_terms (t::ts) = pp_term t ^ "," ^ pp_terms ts

(* compare t s = LESS | EQUAL | GREATER
 * compare_list ts ss = LESS | EQUAL | GREATER
 * requires t, s, ts, ss ground
 *)
fun compare (Con(f,ts)) (Con(g,ss)) =
    (case String.compare(f,g)
      of LESS => LESS
       | EQUAL => compare_list ts ss
       | GREATER => GREATER)
and compare_list (t::ts) (s::ss) =
    (case compare t s
      of LESS => LESS
       | EQUAL => compare_list ts ss
       | GREATER => GREATER)
  | compare_list nil (s::ss) = LESS
  | compare_list (t::ts) nil = GREATER
  | compare_list nil nil = EQUAL

(* substitutions *)
type subst = (var * term) list

val empty : subst = nil

fun subst theta (Con(f,ts)) = Con(f, List.map (subst theta) ts)
  | subst ((x,t)::theta) (Var(y)) =
    if x = y then t else subst theta (Var(y))
  | subst nil (Var(y)) = raise Fail ("undefined variable " ^ y)

fun subst_var nil y = NONE
  | subst_var ((x:var,t)::theta) y =
    if x = y then SOME(t) else subst_var theta y

(* match : subst -> term -> term -> subst option
 * match theta t s = SOME(theta') if theta' extends theta and theta' t = s
 * requires that s is closed
 *)
fun match theta (Var(x)) (s as Con(g,ss)) =
    (case subst_var theta x
      of SOME(t) => match theta t s
       | NONE => SOME((x,s)::theta))
  | match theta (Con(f,ts)) (Con(g,ss)) =
    if f = g then match_list theta ts ss else NONE
and match_list theta nil nil = SOME(theta)
  | match_list theta (t::ts) (s::ss) =
    (case match theta t s
      of SOME(theta') => match_list theta' ts ss
       | NONE => NONE)
  | match_list theta _ _ = NONE

(**********************)
(* Rules of inference *)
(**********************)

(*
 * P1 ... Pn
 * ---------
 * C1 ... Ck
 *
 * represented as Rule([P1,...,Pn],[C1,...,Ck])
 *)
datatype rule = Rule of term list * term list

fun occurs_in (Var(y)) x = (x = y)
  | occurs_in (Con(f,ts)) x = occurs_in_list ts x
and occurs_in_list nil x = false
  | occurs_in_list (t::ts) x = occurs_in t x orelse occurs_in_list ts x

fun rr premises (Var(x)) = occurs_in_list premises x
  | rr premises (Con(f,ss)) = rr_list premises ss
and rr_list premises nil = true
  | rr_list premises (s::ss) =
    rr premises s andalso rr_list premises ss

(* range_restricted (Rule(premises, conclusions)) = true
 * iff every variable in conclusions occurs in at least on premise
 *)
fun range_restricted (Rule (premises, conclusions)) =
    rr_list premises conclusions

end  (* structure Term *)

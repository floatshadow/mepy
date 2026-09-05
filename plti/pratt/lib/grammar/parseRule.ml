open Core

(* §3.2 as a GADT. Each Ref hides the result type of its tail; its process
   function is the proof that the tail and the parsed tree fit together.
   There is no Obj.magic and no Tree.Error masquerading as an arbitrary 'a. *)
type 'a t = { choices : 'a choice list }
and _ choice =
  | End : 'a -> 'a choice
  | Keyword : string * 'a t -> 'a choice
  | Ref : {
      kind : SyntaxKind.t;
      capture : string option;
      label : string;
      bp : int option;
      rest : 'b t;
      process : Tree.located -> 'b -> 'a;
    }
      -> 'a choice
  | Infix : {
      name : string;
      operator : string -> Operator.t option;
      rhs_kind : SyntaxKind.t;
      rest : 'b t;
      process : string -> Tree.located -> 'b -> 'a;
    }
      -> 'a choice

let rule choices = { choices }
let finish value = rule [ End value ]
let keyword name rest = Keyword (name, rest)
let reference ?bp ?capture ?(label = "") kind rest process =
  Ref { kind; capture; label; bp; rest; process }

let capture ?bp kind = rule [ reference ?bp kind (finish ()) (fun tree () -> tree) ]

let rec map : type a b. a t -> f:(a -> b) -> b t =
 fun rule ~f ->
  {
    choices =
      List.map rule.choices ~f:(fun choice ->
          match choice with
          | End value -> End (f value)
          | Keyword (name, rest) -> Keyword (name, map rest ~f)
          | Ref { kind; capture; label; bp; rest; process } ->
              Ref
                {
                  kind;
                  capture;
                  label;
                  bp;
                  rest;
                  process = (fun tree tail -> f (process tree tail));
                }
          | Infix { name; operator; rhs_kind; rest; process } ->
              Infix
                {
                  name;
                  operator;
                  rhs_kind;
                  rest;
                  process = (fun op tree tail -> f (process op tree tail));
                });
  }

(* Sequencing expands the finite rule tree, but never follows named references.
   Thus a recursive grammar still has a finite, inspectable representation. *)
let rec append : type a b c. a t -> b t -> (a -> b -> c) -> c t =
 fun first second f ->
  {
    choices =
      List.concat_map first.choices ~f:(function
        | End value -> (map second ~f:(f value)).choices
        | Keyword (name, rest) -> [ Keyword (name, append rest second f) ]
        | Ref { kind; capture; label; bp; rest; process } ->
            [
              Ref
                {
                  kind;
                  capture;
                  label;
                  bp;
                  rest = append rest second (fun a b -> (a, b));
                  process = (fun tree (a, b) -> f (process tree a) b);
                };
            ]
        | Infix { name; operator; rhs_kind; rest; process } ->
            [
              Infix
                {
                  name;
                  operator;
                  rhs_kind;
                  rest = append rest second (fun a b -> (a, b));
                  process = (fun op tree (a, b) -> f (process op tree a) b);
                };
            ]);
  }

let keyword_choice rule name =
  List.find_map rule.choices ~f:(function
    | Keyword (candidate, rest) when String.equal candidate name -> Some rest
    | _ -> None)

let end_choice rule = List.find_map rule.choices ~f:(function End value -> Some value | _ -> None)

(* A self-reference with no entry threshold denotes a left-hand side already
   parsed by parse_kind. Mapping its tail produces functions to extend that
   left-hand side. The GADT retains the hidden tail type through this map. *)
let after_ref kind rule =
  let choices =
    List.concat_map rule.choices ~f:(function
      | Ref { kind = target; bp = None; rest; process; _ } when SyntaxKind.equal kind target ->
          (map rest ~f:(fun tail lhs -> process lhs tail)).choices
      | _ -> [])
  in
  if List.is_empty choices then None else Some { choices }

let without_self kind rule =
  {
    choices =
      List.filter rule.choices ~f:(function
        | Ref { kind = target; bp = None; _ } -> not (SyntaxKind.equal target kind)
        | _ -> true);
  }

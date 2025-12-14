open Term

(* Reachability in a directed graph *)
(* structural *)
let x = Var "x"
let y = Var "y"
let z = Var "z"
let a = Con ("a", [])
let b = Con ("b", [])
let c = Con ("c", [])
let d = Con ("d", [])
let edge x y = Con ("edge", [ x; y ])
let path x y = Con ("path", [ x; y ])
let rule_E = Rule ([ edge x y ], [ path x y ])
let rule_T = Rule ([ path x y; path y z ], [ path x z ])
let graph_rules = [ rule_E; rule_T ]

let run1 () =
  let ex1_init = [ edge a b; edge b c; edge b d ] in
  Format.printf "init:@.%s@." (State.pp_state ex1_init);
  let ex1_final = Saturate.saturate graph_rules ex1_init in
  Format.printf "final:@.%s@." (State.pp_state ex1_final)
;;

(* Coin exchange *)
(* linear *)
let quarter = Con ("quarter", [])
let dime = Con ("dime", [])
let nickel = Con ("nickel", [])
let rule_Q = Rule ([ quarter ], [ dime; dime; nickel ])
let rule_Qinv = Rule ([ dime; dime; nickel ], [ quarter ])
let rule_D = Rule ([ dime ], [ nickel; nickel ])
let rule_Dinv = Rule ([ nickel; nickel ], [ dime ])
let coin_rules = [ rule_Q; rule_Qinv; rule_D; rule_Dinv ]

let run2 () =
  let ex2_init = [ quarter; nickel ] in
  Format.printf "init:@.%s@." (Federation.pp_state ex2_init);
  let ex2_finals = Linear.iterate coin_rules [ ex2_init ] in
  (* need list of states here *)
  Format.printf "final:@.%s@." (Federation.pp_states ex2_finals)
;;

(* Blocks world *)
(* linear *)
let a = Con ("a", [])
let b = Con ("b", [])
let x = Var "x"
let y = Var "y"
let table = Con ("table", [])
let on x y = Con ("on", [ x; y ])
let holds x = Con ("holds", [ x ])
let empty = Con ("empty", [])
let clear x = Con ("clear", [ x ])
let rule_pickup = Rule ([ empty; clear x; on x y ], [ holds x; clear y ])
let rule_putdown = Rule ([ holds x; clear y ], [ empty; clear x; on x y ])
let blocks_rules = [ rule_pickup; rule_putdown ]

let run3 () =
  let ex3_init = [ empty; clear a; on a b; on b table; clear table ] in
  Format.printf "init:@.%s@." (Federation.pp_state ex3_init);
  let ex3_finals = Linear.iterate blocks_rules [ ex3_init ] in
  Format.printf "final:@.%s@." (Federation.pp_states ex3_finals)
;;

(* Matching parentheses *)
(* ordered *)

let l = Con ("(", [])
let r = Con (")", [])
let rules_parens = [ Rule ([ l; r ], []) ]

let run4 () =
  let ex4_init = [ l; r; l; l; r; r; l; r ] in
  Format.printf "init:@.%s@." (Federation.pp_state ex4_init);
  let ex4_quiescent = Ordered.quiesce rules_parens ex4_init in
  Format.printf "final (quiescent):@.%s@." (Federation.pp_state ex4_quiescent);
  let ex4_all = Ordered.iterate rules_parens [ ex4_init ] in
  Format.printf "final (all):@.%s@." (Federation.pp_states ex4_all)
;;

(* Binary increment *)
(* ordered *)

let b0 = Con ("0", [])
let b1 = Con ("1", [])
let e = Con ("e", [])
let inc = Con ("inc", [])
let rule_inc0 = Rule ([ b0; inc ], [ b1 ])
let rule_inc1 = Rule ([ b1; inc ], [ inc; b0 ])
let rule_ince = Rule ([ e; inc ], [ e; b1 ])
let rules_inc = [ rule_inc0; rule_inc1; rule_ince ]

let run5 () =
  let ex5_init = [ e; b1; b0; b1; inc; inc ] in
  Format.printf "init:@.%s@." (Federation.pp_state ex5_init);
  let ex5_quiescent = Ordered.quiesce rules_inc ex5_init in
  Format.printf "final (quiescent):@.%s@." (Federation.pp_state ex5_quiescent);
  let ex5_all = Ordered.iterate rules_inc [ ex5_init ] in
  Format.printf "final (all):@.%s@." (Federation.pp_states ex5_all)
;;

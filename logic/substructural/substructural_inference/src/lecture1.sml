open Term

(* Reachability in a directed graph *)
(* structural *)
val X = Var("x")
val Y = Var("y")
val Z = Var("z")

val a = Con("a", [])
val b = Con("b", [])
val c = Con("c", [])
val d = Con("d", [])

fun edge(x,y) = Con("edge", [x,y])
fun path(x,y) = Con("path", [x,y])
val rule_E = Rule([edge(X,Y)], [path(X,Y)])
val rule_T = Rule([path(X,Y), path(Y,Z)], [path(X,Z)])

val graph_rules = [rule_E, rule_T]

fun run1 () =
    let
        val ex1_init = [edge(a,b), edge(b,c), edge(b,d)]
        val () = print ("init:\n" ^ State.pp_state ex1_init)
        val ex1_final = Saturate.saturate graph_rules ex1_init
        val () = print ("final:\n" ^ State.pp_state ex1_final)         
    in () end

(* Coin exchange *)
(* linear *)
val quarter = Con("quarter", [])
val dime = Con("dime", [])
val nickel = Con("nickel", [])

val rule_Q = Rule([quarter],[dime,dime,nickel])
val rule_Qinv = Rule([dime,dime,nickel],[quarter])
val rule_D = Rule([dime],[nickel,nickel])
val rule_Dinv = Rule([nickel,nickel],[dime])

val coin_rules = [rule_Q, rule_Qinv, rule_D, rule_Dinv]

fun run2 () =
    let
        val ex2_init = [quarter, nickel]
        val () = print ("init:\n" ^ Federation.pp_state ex2_init ^ "\n")
        val ex2_finals = Linear.iterate coin_rules [ex2_init] (* need list of states here *)
        val () = print ("final:\n" ^ Federation.pp_states ex2_finals ^ "\n")
    in () end

(* Blocks world *)
(* linear *)
val a = Con("a", [])
val b = Con("b", [])
val X = Var("x")
val Y = Var("y")
val table = Con("table", [])

fun on(x,y) = Con("on", [x,y])
fun holds(x) = Con("holds", [x])
val empty = Con("empty", [])
fun clear(x) = Con("clear", [x])

val rule_pickup = Rule([empty, clear(X), on(X,Y)], [holds(X), clear(Y)])
val rule_putdown = Rule([holds(X), clear(Y)], [empty, clear(X), on(X,Y)])

val blocks_rules = [rule_pickup, rule_putdown]

fun run3 () =
    let
        val ex3_init = [empty, clear(a), on(a,b), on(b,table), clear(table)]
        val () = print ("init:\n" ^ Federation.pp_state ex3_init ^ "\n")
        val ex3_finals = Linear.iterate blocks_rules [ex3_init]
        val () = print ("final:\n" ^ Federation.pp_states ex3_finals ^ "\n")
    in () end 

(* Matching parentheses *)
(* ordered *)

val L = Con("(", [])
val R = Con(")", [])

val rules_parens = [Rule([L, R], [])]

fun run4 () =
    let
        val ex4_init = [L, R, L, L, R, R, L, R]
        val () = print ("init:\n" ^ Federation.pp_state ex4_init ^ "\n")
        val ex4_quiescent = Ordered.quiesce rules_parens ex4_init
        val () = print ("final (quiescent):\n" ^ Federation.pp_state ex4_quiescent ^ "\n")
        val ex4_all = Ordered.iterate rules_parens [ex4_init]
        val () = print ("final (all):\n" ^ Federation.pp_states ex4_all ^ "\n")
    in () end
              
(* Binary increment *)
(* ordered *)

val b0 = Con("0", [])
val b1 = Con("1", [])
val e = Con("e", [])
val inc = Con("inc", [])

val rule_inc0 = Rule([b0, inc], [b1])
val rule_inc1 = Rule([b1, inc], [inc, b0])
val rule_ince = Rule([e, inc], [e, b1])

val rules_inc = [rule_inc0, rule_inc1, rule_ince]

fun run5 () =
    let
        val ex5_init = [e, b1, b0, b1, inc, inc]
        val () = print ("init:\n" ^ Federation.pp_state ex5_init ^ "\n")               
        val ex5_quiescent = Ordered.quiesce rules_inc ex5_init
        val () = print ("final (quiescent):\n" ^ Federation.pp_state ex5_quiescent ^ "\n")
        val ex5_all = Ordered.iterate rules_inc [ex5_init]
        val () = print ("final (all):\n" ^ Federation.pp_states ex5_all ^ "\n")
    in () end 

(*
run1();
run2();
run3();
run4();
run5();
*)

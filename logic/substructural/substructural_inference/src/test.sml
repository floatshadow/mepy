structure SaturateTest =
struct

structure S = Saturate
open Term

val X = Var("x")
val Y = Var("y")
val Z = Var("z")

val a = Con("a",[])
val b = Con("b",[])
val c = Con("c",[])
val d = Con("d",[])

fun edge (x,y) = Con("edge", [x,y])
fun node (x) = Con("node", [x])
fun path (x,y) = Con("path", [x,y])
val sym = Rule([edge(X,Y)],[edge(Y,X)])
val refl = Rule([node(X)], [path(X,X)])
val step = Rule([path(X,Y), edge(Y,Z)], [path(X,Z)])

fun test () =
    let
        val bad_refl = Rule([]:term list,[path(X,X)])
        val false = range_restricted bad_refl

        val db0 = State.sort_set
                      [node(a), node(b), node(c), node(d),
                       edge(a,b), edge(b,c), edge(a,c), edge(b,d)]
        val () = TextIO.print ("% db0\n" ^ State.pp_state db0)
                 
        val db1 = S.saturate [sym] db0
        val () = TextIO.print ("% db1\n" ^ State.pp_state db1)
        val db1_expected =
            [
             edge(a,b), edge(a,c), edge(b,a), edge(b,c), edge(b,d), edge(c,a), edge(c,b), edge(d,b),
             node(a), node(b), node(c), node(d)
            ]

        val true = (db1 = db1_expected)

        val db2 = S.saturate [sym,refl,step] db0
        val db2_expected =
            [
             edge(a,b), edge(a,c), edge(b,a), edge(b,c), edge(b,d), edge(c,a), edge(c,b), edge(d,b),
             node(a), node(b), node(c), node(d),
             path(a,a), path(a,b), path(a,c), path(a,d), path(b,a), path(b,b), path(b,c), path(b,d),
             path(c,a), path(c,b), path(c,c), path(c,d), path(d,a), path(d,b), path(d,c), path(d,d)
            ]
        val () = TextIO.print ("% db2\n" ^ State.pp_state db2)
        val true = (db2 = db2_expected)
        val () = TextIO.print ("All tests passed!\n")
    in
        ()
    end

end (* structure SaturateTest *)

structure LinearTest =
struct

open Term

val quarter = Con("quarter", [])
val dime = Con("dime", [])
val nickel = Con("nickel", [])

val q = Rule([quarter],[dime,nickel,nickel])
val d = Rule([dime],[nickel,nickel])

fun test_coin_exchange () =
    let
        val ex0 = Linear.apply_rule q [quarter]
        val ex1 = Federation.sort [State.sort_multiset [quarter,dime]]
        val () = TextIO.print ("# ex1\n" ^ Federation.pp_states ex1 ^ "\n")
        val ex2 = Linear.apply_rule d (State.sort_multiset [quarter,dime])
        val () = TextIO.print ("# ex2\n" ^ Federation.pp_states ex2 ^ "\n")
        val ex3 = Federation.sort (List.concat (List.map (Linear.apply_rule d) ex2))
        val () = TextIO.print ("# ex3\n" ^ Federation.pp_states ex3 ^ "\n")
        val ex4 = Linear.iterate [q,d] ex1
        val () = TextIO.print ("# ex4\n" ^ Federation.pp_states ex4 ^ "\n")
        val ex4_expected =
            [
             [dime, dime, nickel, nickel],
             [dime, nickel, nickel, nickel, nickel],
             [dime, quarter],
             [nickel, nickel, nickel, nickel, nickel, nickel],
             [nickel, nickel, quarter]
            ]
        val true = (ex4 = ex4_expected)
        val () = TextIO.print ("Coin exchange tests passed!\n")
    in
        ()
    end

fun on(x,y) = Con("on", [x,y])
fun clear(x) = Con("clear", [x])
val empty = Con("empty", [])
fun holds(x) = Con("holds", [x])

val table = Con("table", [])
val a = Con("a", [])
val b = Con("b", [])
val c = Con("c", [])

val X = Var "X"
val Y = Var "Y"

val pickup = Rule([empty, clear(X), on(X,Y)], [holds(X), clear(Y)])
val putdown = Rule([holds(X), clear(Y)], [empty, clear(X), on(X,Y)])

fun test_blocksworld () =
    let
        val s0 = [[empty, on(b,table), on(a,b), clear(a), clear(table)]]
        val () = TextIO.print ("# s0\n" ^ Federation.pp_states s0 ^ "\n")
        val s1 = Linear.iterate [pickup,putdown] s0
        val () = TextIO.print ("# s1\n" ^ Federation.pp_states s1 ^ "\n")
        val s1_expected =
            [
             [clear(a), clear(b), empty, on(a,table), on(b,table)],
             [clear(a), clear(table), empty, on(a,b), on(b,table)],
             [clear(a), clear(table), holds(b), on(a,table)],
             [clear(b), clear(table), empty, on(a,table), on(b,a)],
             [clear(b), clear(table), holds(a), on(b,table)]
            ]
        val true = (s1 = s1_expected)
        val () = TextIO.print ("Blocks world tests passed!\n")
    in
        ()
    end

fun test () =
    let
        val () = test_coin_exchange ()
        val () = test_blocksworld ()
        val () = TextIO.print ("All tests passed!\n")
    in
        ()
    end

end (* structure LinearTest *)

structure OrderedTest =
struct

structure O = Ordered
open Term

val b0 = Con("b0", [])
val b1 = Con("b1", [])
val e = Con("e", [])
val inc = Con("inc", [])

val inc_b0 = Rule([b0, inc], [b1])
val inc_b1 = Rule([b1, inc], [inc, b0])
val inc_e = Rule([e, inc], [e, b1])

fun test_increment () =
    let
        val s5 = [e, b1, b0, b1]
        val ex5 = Ordered.iterate [inc_b0, inc_b1, inc_e] [s5]
        val () = TextIO.print ("# ex5\n" ^ Federation.pp_states ex5 ^ "\n")
        val ex6 = Ordered.iterate [inc_b0, inc_b1, inc_e] [s5 @ [inc]]
        val () = TextIO.print ("# ex6\n" ^ Federation.pp_states ex6 ^ "\n")
        val ex6_expected =
            [
             [e, b1, b0, b1, inc],
             [e, b1, b0, inc, b0],
             [e, b1, b1, b0]
            ]
        val true = (ex6 = ex6_expected)
        val () = TextIO.print ("Increment test passed!\n")
    in
        ()
    end

val L = Con("(", [])
val R = Con(")", [])
val LR = Rule([L,R], [])

fun test_vanish () =
    let
        val m1 = Ordered.iterate [LR] [[L,L,R,L,R,R]]
        val () = TextIO.print ("# m1\n" ^ Federation.pp_states m1 ^ "\n")
        val m1_expected =
            [
             [],
             [L, L, R, L, R, R],
             [L, L, R, R],
             [L, R]
            ]
        val true = (m1 = m1_expected)
        val m2 = Ordered.iterate [LR] [[R,L,L,R,L,R,R,L]]
        val () = TextIO.print ("# m2\n" ^ Federation.pp_states m2 ^ "\n")
        val m2_expected =
            [
             [R, L],
             [R, L, L, R, L, R, R, L],
             [R, L, L, R, R, L],
             [R, L, R, L]
            ]
        val true = (m2 = m2_expected)
        val () = TextIO.print ("Vanishing parentheses test passed!\n")
    in
        ()
    end

val T = Con("T", [])
val S = Con("S", [])
val B = Con("<", [])
val E = Con(">", [])

val T1 = Rule([L,R], [T])
val T2 = Rule([L,T,R], [T])
val T3 = Rule([T,T], [T])
val S0 = Rule([B,E], [S])
val S1 = Rule([B,T,E], [S])

fun test_parse () =
    let
        val p1 = Ordered.iterate [T1,T2,T3,S0,S1] [[B,L,L,R,L,R,R,E]]
        val () = TextIO.print ("# p1\n" ^ Federation.pp_states p1 ^ "\n")
        val p1_expected =
            [
             [B, L, L, R, L, R, R, E],
             [B, L, L, R, T, R, E],
             [B, L, T, L, R, R, E],
             [B, L, T, R, E],
             [B, L, T, T, R, E],
             [B, T, E],
             [S]
            ]
        val true = (p1 = p1_expected)
                   
        val p2 = Ordered.iterate [T1,T2,T3,S0,S1] [[B,R,L,L,R,L,R,R,L,E]]
        val () = TextIO.print ("# p2\n" ^ Federation.pp_states p2 ^ "\n")
        val p2_expected =
            [
             [B, R, L, L, R, L, R, R, L, E],
             [B, R, L, L, R, T, R, L, E],
             [B, R, L, T, L, R, R, L, E],
             [B, R, L, T, R, L, E],
             [B, R, L, T, T, R, L, E],
             [B, R, T, L, E]
            ]
        val true = (p2 = p2_expected)

        val p3 = Ordered.quiesce [T1,T2,T3,S0,S1] [B,L,L,R,L,R,R,E]
        val () = TextIO.print ("# p3: " ^ Federation.pp_state p3 ^ "\n")
        val p3_expected =
            [ S ]
        val true = (p3 = p3_expected)

        val p4 = Ordered.quiesce [T1,T2,T3,S0,S1] [B,R,L,L,R,L,R,R,L,E]
        val () = TextIO.print ("# p4: " ^ Federation.pp_state p4 ^ "\n")
        val p4_expected =
            [B, R, T, L, E]
        val true = (p4 = p4_expected)
        val () = TextIO.print ("Parsing example passed!\n")
    in
        ()
    end

fun test () =
    let
        val () = test_increment ()
        val () = test_vanish ()
        val () = test_parse ()
        val () = TextIO.print ("All examples passed!\n")
    in
        ()
    end

end (* structure OrderedTest *)

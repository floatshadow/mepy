structure HW1 :> HW1 =
struct

open Term

(* Problem 1: Parsing in Ordered Inference *)
(*
   Task 1: Describe the encoding of the grammar productions
   as ordered inference rules

   ... here ...
 *)
(* Problem 1 vocabulary *)
val S = Con("S", [])
val T = Con("T", [])
val a = Con("a", [])
val b = Con("b", [])
val $ = Con("$", [])
val L = Con("(", []) (* for Task 4 *)
val R = Con(")", [])

val task2 = []
val task3 = []
val task4 = []

(* Problem 2: Parsing in Structural Inference *)
(*
   Task 5: Describe the encoding of the grammar productions
   as structural inference rules

   ... here ...
*)
(* Problem 2 vocabulary *)
(* S, T, a, b, L, R as for Problem 1 *)

val zero = Con("0", [])
fun succ n = Con("s", [n])
fun num n = Con("num", [n])
fun ext(i, a, j) = Con("ext", [i, a, j])
val x = Var("x")
val y = Var("y")
val z = Var("z")
val u = Var("u")

val task6 = []
val task7 = []
val task8 = []

(* Problem 3: The 2-Counter Minsky Machine in Linear Inference *)
(*
   Task 9: Describe the encoding of the Minsky machine programs
   as linear inference rules

   ... here ...
 *)
(* vocabulary for Problem 3 *)
(* zero, succ as in Problem 2 *)
val r1 = Con("r1", [])
val r2 = Con("r2", [])
fun reg(r,n) = Con("reg", [r,n])
fun pc(i) = Con("pc", [i])
val k = Var("k")
val one = succ zero
val two = succ one
val three = succ two
val four = succ three

val task10 = []
val task11 = []
val task12 = []

end

from z3 import *


# MC91 function

n = Int("n")
r = Int("r")
# Predicate, for input n, if r is the return value of Mc91 function
Mc91 = Function("Mc91", IntSort(), IntSort(), BoolSort())

solver = Solver()

# Mc91(n, r) <- n > 100 /\ r = n - 10
solver.add(Implies(And(n > 100, r == n - 10), Mc91(n , r)))
# Mc91(n, r) <- not (n > 100) /\ Mc91(n + 11, r') /\ Mc91(r', r)
rp = Int("r_prime")
solver.add(Implies(And(Not(n > 100), And(Mc91(n + 11, rp), Mc91(rp, r))), Mc91(n, r)))
# r = 91 <- n <= 101 /\ Mc91(n, r)
solver.add(Implies(And(n <= 101, Mc91(n, r)), r == 91))

if solver.check() == sat:
    print(solver.model())
else: 
    print("unsat")


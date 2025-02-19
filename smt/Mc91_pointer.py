from z3 import *

# Mc91 function can be written with pointers
# void mc91p( int n , int * r) {
#   if (n > 100) *r = n - 10;
#   else { int s; mc91p(n + 11, &s); mc91p(s, r); }
# }

# See https://dl.acm.org/doi/pdf/10.1145/3462205

# Memory Model: Array
memory_model_sort = ArraySort(IntSort(), IntSort())
# initial and transformed memory arrays
h = Array("h", IntSort(), IntSort())
hp = Array("h_prime", IntSort(), IntSort())

n = Int("n")
r = Int("r")

Mc91p = Function("Mc91p", 
            IntSort(), IntSort(), memory_model_sort, memory_model_sort,
            BoolSort())

solver = Solver()

solver.add(Implies(And(n > 100, hp == Store(h, r, n - 10)), Mc91p(n, r, h, hp)))

# exists quantifier
sp = Int("s_prime")
hpp = Array("h_prime_prime", IntSort(), IntSort())
solver.add(Implies(And(Not(n > 100), Exists([sp, hpp], And(Mc91p(n + 11, sp, h, hp), Mc91p(hpp[sp], r, hpp, hp)))), Mc91p(n, r, h, hp)))

# try to find a counterexmaple that result is not 91
solver.add(Implies(And(n <= 101, Mc91p(n, r, h, hp)), hp[r] != 91))


if solver.check() == sat:
    print(solver.model())
else:
    print("proved")

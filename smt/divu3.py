from z3 import *

# From CMU 15-811: Verifying Complex Systems
# SMT Assignment Question 2

# Figure 10-45 of Hacker’s Delight describes the following optimization that computes `n / k` for the `k = 3` case:

# uint32_t divu3(uint32_t n)
# {
#   	uint32_t r = (0x55555555 * n + (n >> 1) - (n >> 3)) >> 30;
#   	return (n - r) * 0xaaaaaaab;
# }

n = BitVec("n", 32)
k = BitVecVal(3, 32)

solver = Solver()

r = BitVec("r", 32)
magic5 = BitVecVal(int("0x55555555", 16), 32)

solver.add(r == LShR(magic5 * n + LShR(n, 1) - LShR(n ,3), 30))

div3u = BitVec("div3u", 32)
magicab = BitVecVal(int("0xaaaaaaab", 16), 32)
solver.add(div3u == (n - r) * magicab)

# find counterexample
solver.add(div3u != UDiv(n, k))

if solver.check() == sat:
    print(solver.model())
else:
    print("proved")

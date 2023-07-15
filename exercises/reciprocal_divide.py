from z3 import *

# From CMU 15-811: Verifying Complex Systems
# SMT Assignment Question 1

# The [Jitk paper](https://syslab.cs.washington.edu/papers/jitk-osdi14.pdf from OSDI’14 (Figure 11; Section 3.2.2) describes an incorrect optimization in the Linux kernel. 
# Consider unsigned integer division n / k, where n is a 32-bit unsigned integer and k is a 32-bit unsigned constant. 
# The incorrect optimization tries to avoid such a division on the critical path by using two steps:

# 1. precompute a 32-bit unsigned integer `R` using `compute_R`; and
# 2. compute the result using `reciprocal_divide(n, R)`, which only uses multiplication and shift.

# In particular, `R` is precomputed as:

# uint32_t compute_R(uint32_t k) 
# {
#	    uint64_t k64 = (uint64_t)k;
#	    return (uint32_t)(((UINT64_C(1) << 32) + (k64 - 1)) / k64);
# }

# and `reciprocal_divide` is implemented as extracting the high 32 bits of the 64-bit product of `n` and `R`:

# uint32_t reciprocal_divide(uint32_t n, uint32_t R)
# {
# 	    return (uint32_t)(((uint64_t)n * (uint64_t)R) >> 32);
# }

# Take `42 / 3` as an example: precomputing `R` gives `((1ULL << 32) + (3 - 1)) / 3 = 1431655766` and `reciprocal_divide(42, 1431655766)` gives `14`. 
# Unfortunately, this optimization is buggy on some `n` and `k`, as described by [commit aee636c4](https://github.com/torvalds/linux/commit/aee636c4809fa54848ff07a899b326eb1f9987a2).


# This is an machine integer arithmetic
n = BitVec("n", 32)
k = BitVecVal(3, 32)
R = BitVec("R", 32)

solver = Solver()

# uint64_t k64 = (uint64_t)k
k64 = BitVec("k64", 64)
solver.add(k64 == ZeroExt(32, k))
# (uint32_t)(((UINT64_C(1) << 32) + (k64 - 1)) / k64);
UINT64_C_1 = BitVecVal(1, 64)
solver.add(R == Extract(31, 0, UDiv((UINT64_C_1 << 32) + (k64 - 1), k64)))

# reciprocal_divaide
# try to find a n that n / k does not equal to this algorithm
solver.add(UDiv(n, k) != Extract(31, 0, LShR(ZeroExt(32, n) * ZeroExt(32, R), 32))) 


if solver.check() == sat:
    print(solver.model())
else:
    print("proved")

# z3 gives a model n = 3237092663
# n / k = 1079030887
# optimization algorithm result = 107903088

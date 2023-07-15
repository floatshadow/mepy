from z3 import *

# From CMU 15-811: Verifying Complex Systems
# SMT Assignment Question 5

# Finally, ARM supports an “inline barrel shifter”, meaning that the arguments to many instructions can be rotated or shifted essentially for free.
# As a result, when the SHA specification says to compute:

# Sigma1(x) = RotateRight(x, 6) ^ RotateRight(x, 11) ^ RotateRight(x, 25)
# OpenSSL computes it lazily as:

# Sigma1(x) = RotateRight((x ^ RotateRight(x, 5)) ^ RotateRight(x, 19), 6)

x = BitVec("x", 32)

solver = Solver()
spec = BitVec("spec", 32)
solver.add(spec == RotateRight(x, 6) ^ RotateRight(x, 11) ^ RotateRight(x, 25))

openssl = BitVec("openssl", 32)
solver.add(openssl == RotateRight((x ^ RotateRight(x, 5)) ^ RotateRight(x, 19), 6))

# try to find a counterexample
solver.add(spec != openssl)

if solver.check() == sat:
    print(solver.model())
else:
    print("proved")


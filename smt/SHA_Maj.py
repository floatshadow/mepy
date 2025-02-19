from z3 import *

# From CMU 15-811: Verifying Complex Systems
# SMT Assignment 4

#Another example is the SHA function `Maj` which computes a bitwise majority function:

# Maj(x, y, z) = (x & y) ^ (x & z) ^ (y & z)
#which OpenSSL computes as:

# Maj(x, y, z) = ((y ^ z) & (x ^ y)) ^ y

x = BitVec("x", 32)
y = BitVec("y", 32)
z = BitVec("z", 32)

solver = Solver()

spec = BitVec("spec", 32)
solver.add(spec == (x & y) ^ (x & z) ^ (y & z))

openssl = BitVec("openssl", 32)
solver.add(openssl == ((y ^ z) & (x ^ y)) ^ y)

solver.add(spec != openssl)

if solver.check() == sat:
    print(solver.model())
else:
    print("proved")

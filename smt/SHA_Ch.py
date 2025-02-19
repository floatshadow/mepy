from z3 import *

# # From CMU 15-811: Verifying Complex Systems
# SMT Assignment Question 3

# The SHA specification defines a Ch function as:

# Ch(x, y, z) = (x & y) ^ (~x & z)
# i.e., as x AND y exclusive-or with not x AND z. If you look carefully at the OpenSSL code, you’ll see that they compute it as:

# Ch(x, y, z) = ((y ^ z) & x) ^ z

x = BitVec("x", 32)
y = BitVec("y", 32)
z = BitVec("z", 32)

solver = Solver()

spec = BitVec("spec", 32)
solver.add(spec == (x & y) ^ (~x & z))

openssl = BitVec("openssl", 32)
solver.add(openssl  == ((y ^ z) & x) ^ z)

# try to find a counterexample
solver.add(spec != openssl)

if solver.check() == sat:
    print(solver.model())
else:
    print("proved")

# in SHA specification, CH needs:
#   - 2 and
#   - 1 xor
#   - 1 not
# in OpenSSL impl, Ch needs:
#   - 1 and
#   - 2 xor
# We can see that OpenSSL version need 1 less instruction.

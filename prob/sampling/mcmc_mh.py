# MCMC Metropolis-Hastings
# https://bocaiwen.github.io/Metropolis-Hastings.html
import math
import random

# Target distribution
# var lr = function() {
#   var x = gaussian({mu:0, sigma:1})
#   var y = x*x
#   condition(y>20)
#   condition(y<25)
#   return y
# }
#
# chi-square distribution
#   chi_k(x) = 1 / (2^(k / 2) * gamma(k / 2)) * x^(k/2 - 1) * exp(-x/2)
# Given condition y > 20 and y < 25, p(y) ∝ chi_1(y)
def eval_unnormalized_target_distribution_at(z):
  assert z > 20 and z < 25, "z must be in (20, 25)"
  chi1 = 1 / ( math.sqrt(2 * math.pi * z) ) * math.exp(-z/2)
  return chi1

# Proposal distrbution q(z* | z) ~ U(20, 25)
def sample_proposal_distribution(z):
  z_next = random.random()
  return 5 * z_next + 20

def eval_proposal_distribution_at(z_next, z_current):
  assert z_next > 20 and z_next < 25, "z must be in (20, 25)"
  return 1 / 5


if __name__ == "__main__":
  # number of samples
  n = 10000

  # initial state
  z = 21
  samples = [z]
  for _ in range(n):
    z_next = sample_proposal_distribution(z)
    qznext_z = eval_proposal_distribution_at(z_next, z)
    qz_znext = eval_proposal_distribution_at(z, z_next)
    tilde_pznext = eval_unnormalized_target_distribution_at(z_next)
    tilde_pz = eval_unnormalized_target_distribution_at(z)
    alpha = min(1, (tilde_pznext * qz_znext) / (tilde_pz * qznext_z))
    u = random.random()
    if u <= alpha:
      z = z_next
    samples.append(z)

  # expectation
  epz = sum(samples) / len(samples)
  print(f"num_samples = {len(samples)}, expectation = {epz}")

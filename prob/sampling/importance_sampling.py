# importance sampling
# https://bocaiwen.github.io/importance_sampling.html
import random
import math

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

# Proposal distrbution q(y) ~ U(20, 25)
# What we have q(x) ~ U(0, 1)
#
#   x = \int_{20}^y p(\hat{y}) d\hat{y} = \int_{20}^y 1/5 d\hat{y} = (y - 20)/5
#   y = 5x + 20
def sample_proposal_distribution():
  x = random.random()
  return 5 * x + 20

def eval_proposal_distribution_at(z):
  assert z > 20 and z < 25, "z must be in (20, 25)"
  return 1 / 5

if __name__ == "__main__":
  # number of samples
  n = 10000

  tilde_pzs = []
  qzs = []
  samples = []
  for _ in range(n):
    z = sample_proposal_distribution()
    qz = eval_proposal_distribution_at(z)
    tilde_pz = eval_unnormalized_target_distribution_at(z)
    tilde_pzs.append(tilde_pz)
    qzs.append(qz)
    samples.append(z)

  weight_normalize_factor = sum(tilde_pz / qz for tilde_pz, qz in zip(tilde_pzs, qzs))
  weights = [tilde_pz / (weight_normalize_factor * qz) for tilde_pz, qz in zip(tilde_pzs, qzs)]
  epz = sum(w * z for w, z in zip(weights, samples))
  # expectation
  print(f"num_samples = {len(samples)}, expectation = {epz}")


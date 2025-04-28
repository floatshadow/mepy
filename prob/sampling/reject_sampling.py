# accept-reject sampling
# https://bocaiwen.github.io/accept-reject-sampling.html
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
#
# Choose constant k = 2
def sample_proposal_distribution():
  x = random.random()
  return 5 * x + 20

def eval_proposal_distribution_at(z):
  assert z > 20 and z < 25, "z must be in (20, 25)"
  return 1 / 5

def sample_uniform_0_kq(k, qz):
  # sample u ~ U(0, k * q(z))
  u = random.random()
  return u * k * qz

if __name__ == "__main__":
  # number of samples
  n = 10000000

  # constant k
  k = 2

  samples = []
  for _ in range(n):
    z0 = sample_proposal_distribution()
    qz0 = eval_proposal_distribution_at(z0)
    u0 = sample_uniform_0_kq(k, qz0)
    tilde_pz0 = eval_unnormalized_target_distribution_at(z0)
    if u0 <= k * tilde_pz0:
      samples.append(z0)

  # expectation
  epz = sum(samples) / len(samples)
  print(f"num_samples = {len(samples)}, expectation = {epz}")


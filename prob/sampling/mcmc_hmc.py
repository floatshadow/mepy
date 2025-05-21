# Hamiltonian Monte Carlo.
import numpy as np
from tqdm import tqdm

# WebPPL program:
#
# var lr = function() {
#  var x = gaussian({mu:0, sigma:1})
#  var y = gaussian({mu:1, sigma:2})
#  factor(-(x + y - 5) * (x + y - 5));
#  return y
# }

def gussian_log_prob(x, mu, sigma):
  return - np.log(sigma) - 0.5 * np.log(2 * np.pi) - 0.5 * ((x - mu) / sigma) ** 2


def gradient_gussian_log_prob(x, mu, sigma):
  return - (x - mu) / (sigma ** 2)


def potential_energy(position):
  # U(X) = -log γ(X)
  x, y = position
  # sample
  log_prior_x = gussian_log_prob(x, 0, 1)
  log_prior_y = gussian_log_prob(y, 1, 2)
  # factor
  log_factor = - (x + y - 5) ** 2
  return - (log_prior_x + log_prior_y + log_factor)


def gradient_potential_energy(position):
  x, y = position
  # sample
  grad_log_prior_x = gradient_gussian_log_prob(x, 0, 1)
  grad_log_prior_y = gradient_gussian_log_prob(y, 1, 2)
  # factor
  grad_factor_x = -2 * (x + y - 5)
  grad_factor_y = -2 * (x + y - 5)
  return np.array([grad_log_prior_x + grad_factor_x,
                   grad_log_prior_y + grad_factor_y], dtype=np.float32)


def hamiltonian_mc():
  num_samples = 100000
  num_steps = 15
  step_size = 0.01
  samples = []

  # position X = x, y
  # initial position
  position = np.array([0, 0], dtype=np.float32)

  mass_mat = np.eye(2, dtype=np.float32)
  def hamiltonian(position, momentum):
    # H(X, R) = U(X) + K(R)
    # U(X) = potential energy
    # K(R) = kinetic energy
    #   = 1/2 R^T M^{-1} R
    #   = 1/2 R^T R
    UX = potential_energy(position)
    KR = 0.5 * np.dot(momentum, np.dot(np.linalg.inv(mass_mat), momentum))
    return UX + KR

  for _ in tqdm(range(num_samples)):
    # 1. perform the Gibbs update to sample initial momentum
    # R_0 ∼ π(R | X_{s−1}) = π(R)
    # 
    # π(R) = 1/Z γ(R) = 1 / Z exp(−1/2 R^T M^{−1} R) ∝ Normal(R; 0, M)
    momentum = np.random.multivariate_normal(mean=[0, 0], cov=mass_mat)
    momentum0 = momentum.copy()
    position0 = position.copy()
    H = hamiltonian(position0, momentum0)


    # 2. Perform an MH update using Hamiltonian Dynamics.
    # Numerical integration with Leap frog
    # Compute the trajectory of the Hamiltonian system
    # dX/dt = M^{-1} R
    # dR/dt = -∇_X U(X)
    momentum += 0.5 * step_size * gradient_potential_energy(position)

    for step in range(num_steps):
      position += step_size * np.dot(np.linalg.inv(mass_mat), momentum)
      if step < num_steps - 1:
        momentum += step_size  * gradient_potential_energy(position)

    momentum += 0.5 * step_size * gradient_potential_energy(position)

    momentum = -momentum
    H_prime = hamiltonian(position, momentum)

    # MH update
    log_alpha = np.minimum(0.0, H_prime - H)
    if np.log(np.random.uniform()) < log_alpha:
      samples.append(position)
    else:
      position = position0
      samples.append(position)

  return np.array(samples)

if __name__ == "__main__":
  warm_up = 1000
  samples = hamiltonian_mc()
  samples = samples[warm_up:, 1]
  num_samples = len(samples)
  epy = np.mean(samples)
  print(f"num_samples = {num_samples}, expectation of y = {epy}")

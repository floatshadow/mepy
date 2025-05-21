# Sequential Monte Carlo (SMC)
# There is a strange road in X-Y axis. 
# The upper boundary and the lower boundary of this road are described by 
# functions u(x) = sin(x + b1) + 2 + kx, l(x) = sin(x + b2) - 2 - kx, respectively, 
# where b1, b1 ~ uniform(-π, π) and k ~ uniform(0, 1). 

# There is a car at (0, y0) point where y0 ~ uniform(-1, 1). 
# This car moves rightward along line y = y0 in the following way. 
#   1. A random distance d ~ uniform(0, 1) is selected and then the car moves d unit rightward. 
#   2. The radar on the car reports the distances between the car and the two boundaries.
#      Formally, let (x, y) be the coordinate of the car. 
#      The radar will report two numbers u(x) - y + ε1 and y - l(x) + ε2,
#      where ε1, ε2 ~ N(0, 1) are random noises.
#   3. Go back to Step 1. Note that the values of are independently sampled in each turn. 

import numpy as np
from tqdm import tqdm


def sequential_mc_bootstrap_filter(observations):
  # internal states X_{0:t}
  # observations Y_{1:t}
  # p(x_t | y_{1:t-1})
  # given x_t, y_{0:t-1} and y_t are conditionally independent
  #                              p(y_t | x_t) * p(x_t | y_{1:t-1}) 
  # --> p(x_t | y_{1:t}) = ------------------------------------------- (filter)
  #                         \int p(y_t | x_t) * p(x_t | y_{1:t-1}) dx_t
  #
  # --> p(x_{t+1} | y_{1:t}) = \int p(x_{t+1} | x_t) * p(x_t | y_{1:t}) dx_t (prediction)
  #
  # --> p(x_{t+1} | y_{1:t}) = \int p(x_{t+1} | x_t, y_{1:t}) * p(x_t | y_{0:t}) dx_t
  #                          = \int p(x_{t+1} | x_t)          * p(x_t | y_{0:t}) dx_t
  #                          = \int p(x_{t+1} | x_t)          * p(x_t | y_t,  y_{1:t-1}) dx_t
  #                         \int p(x_{t+1} | x_t) * p(y_t | x_t) * p(x_t | y_{1:t-1}) dx_t
  #                         ------------------------------------------------------------ (update)
  #                            \int p(y_t | x_t) * p(x_t | y_{1:t-1}) dx_t
  num_samples = 1000000
  num_steps = 10

  # initialize particles
  # since initial state has no observation, all particles are equally likelihood (weight)
  X = {
    'y0': np.random.uniform(-1, 1, num_samples),
    'b1': np.random.uniform(-np.pi, np.pi, num_samples),
    'b2': np.random.uniform(-np.pi, np.pi, num_samples),
    'k': np.random.uniform(0, 1, num_samples),
    'x': np.zeros(num_samples) 
  }
  weight = np.ones(num_samples) / num_samples

  for t in tqdm(range(num_steps), desc="(re-)sampling i-th step"):
    # sampling ancestor index
    index = np.arange(num_samples)
    At = np.random.choice(index, size=num_samples, p=weight)
    # generate proposal / resampling
    XAt = {
      'y0': X['y0'][At],
      'b1': X['b1'][At],
      'b2': X['b2'][At],
      'k': X['k'][At],
      'x': X['x'][At]
    }
    ds = np.random.uniform(0, 1, num_samples)
    XAt['x'] += ds
    # likelihood / weights
    # u(x) = sin(x + b1) + 2 + kx, l(x) = sin(x + b2) - 2 - kx
    predict_upper = np.sin(XAt['x'] + XAt['b1']) + 2 + XAt['k'] * XAt['x']
    predict_upper_d = predict_upper - XAt['y0']
    upper_likelihood = np.exp(-0.5 * (predict_upper_d - observations[t, 0])**2)
    predict_lower = np.sin(XAt['x'] + XAt['b2']) - 2 - XAt['k'] * XAt['x']
    predict_lower_d = XAt['y0'] - predict_lower
    lower_likelihood = np.exp(-0.5 * (predict_lower_d - observations[t, 1])**2)

    unormalized_weight = upper_likelihood * lower_likelihood
    weight = unormalized_weight / np.sum(unormalized_weight)
    X = XAt

  # infer expectation of y0
  exy0 = np.sum(weight * X['y0'])
  return exy0

if __name__ == "__main__":
  radar_readings = np.array([
    1.2160350962649178, 2.5996692706510114,
    1.8590117093528153, 3.305528270926983,
    2.5674877574407637, 4.003078529146716,
    3.658086483432631, 4.9213352819961536,
    4.137317602890782, 5.217629866321083,
    4.283588274331887, 5.108091095550762,
    3.890954207633913, 4.689686107671097,
    3.7988707199283573, 4.632903557205479,
    3.6999357059145077, 4.612007243281997,
    3.7944959189850302, 4.952352727366396,
  ]).reshape(-1, 2)
  
  exy0 = sequential_mc_bootstrap_filter(radar_readings)
  print(f"expectation of y0 = {exy0}")
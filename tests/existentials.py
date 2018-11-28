from nptyping import *
import numpy as np

# a nontrivial operation (unique, where, etc)
def magic(x: array[a]) -> array[_b]:
    return np.zeros(3) # callee makes choice of b

a = magic(np.zeros(1))
b = magic(np.zeros(2))
c = a + b

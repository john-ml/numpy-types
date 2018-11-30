from nptyping import *
import numpy as np

# a nontrivial operation (unique, where, etc)
def magic(p: bool, x: array[a]) -> array[_b]:
    return np.zeros(3) if p else np.zeros(4) # callee chooses b

# not possible: caller sees (_ : array[b]) + (_ : array[b'])
a = magic(True, np.zeros(1)) + magic(True, np.zeros(2))

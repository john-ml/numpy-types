from nptyping import *
import numpy as np

def f(a: int) -> a + 1:
    return a + 1

# ok -- a no longer in scope
a = True 

# Can't unify 'Fun(((a : int)), ((a : int) + 1))' with 'array[1]'
f = np.ones(1)+1+1+1+1+1+1+1+1+1+1

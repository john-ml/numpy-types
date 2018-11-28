from nptyping import *
import numpy as np

def f(p: bool, n: int) -> array[n + 2]:
    if p:
        n = 1 + n
        r = np.zeros(n)
    else:
        r = np.zeros(n + 1)
    return np.ones(r.shape[0] + 1) + np.zeros(n + 1 if p else n + 2)

a = f(True, 3) * np.ones(5)
print(a)

def g(p: bool, a: int, b: array[a]) -> array[a + 1]:
    if p:
        return np.zeros(1 + a)
    else:
        # Unsatisfiable constraint: ForAll([p, a],
        #        Implies(And(True, Not(p)), And(True, a + 2 == a + 1)))
        return np.zeros(b.shape[0] + 1) + np.zeros(a + 2)

# no runtime error
print(g(True, 3, np.zeros(3)))

# runtime error
print(g(False, 3, np.zeros(3)))

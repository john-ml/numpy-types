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
        # return np.zeros(b.shape[0] + 1) + np.zeros(a + 2)
        return np.zeros(b.shape[0] + 1) + np.zeros(a + 1)

# no runtime error
print(g(True, 3, np.zeros(3)))

# runtime error
print(g(False, 3, np.zeros(3)))

def h(a: int, b: int) -> array[a]:
    if a == b:
        return np.zeros(b) # OK: array[a] ~ array[b] implied by a == b
    else:
        return np.zeros(a)

def j(a: int) -> array[5]:
    # Unsatisfiable constraint: ForAll(a,
    #        Implies(And(True, And(a >= 0, a < 2)),
    #                And(True, a + 5 == 5)))
    # if 0 <= a and a < 2:
    if 0 <= a and a < 1:
        return np.zeros(a + 5)
    else:
        return np.zeros(5)

def k(a: int) -> array[3]:
    assert a >= 0
    if a < 1:
        # OK: aarray[a + 3] ~ array[3] implied by a >= 0 /\ a < 1
        return np.zeros(a + 3)

def l(a: int) -> array[3]:
    if a > 0:
        return np.zeros(3)

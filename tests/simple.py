from nptyping import *
import numpy as num

def f(p: bool, n: int) -> n + 2:
    if p:
        n = 1 + n
    else:
        pass
    return n + 1 if p else n + 2

a = 3
a = f(True, 3)
b = num.zeros(a)
c = num.zeros(f(True, f(False, 1))) + b
d = num.zeros((1, 2))
e = num.zeros((100, 100, 1000))

u = num.zeros(100)
v = num.zeros(100)
u = (u + v) * v
print(u)

u = u + 1
print(u)

from nptyping import *
import numpy as np

a = np.zeros((3, 4,))
b = np.zeros(1)
c = np.ones(2)
d = b + c
e = a + b

# Can't unify 'array[3, 4]' with 'array[2]' (unbroadcastable dimensions)
# f = a + c

g = np.zeros((8, 1, 6, 1))
h = np.ones((7, 1, 5))
i = g * h # OK. i: array[8, 7, 6, 5]

# Can't unify 'array[8, 7, 6]' with 'array[8, 7, 6, 5]' (unbroadcastable dimensions)
# j = np.zeros((8, 7, 6)) + i

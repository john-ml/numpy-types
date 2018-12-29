from nptyping import *
import numpy as np

a = np.zeros((3, 4, 5, 6))
b = a[0, :, 3:4] # OK. b : array[4, 1, 6]

# Can't unify 'array[4, 1, 6]' with 'array[1, 2]' (unbroadcastable dimensions)
# c = b + np.zeros((1, 2))

# Too many indices for array
c = b[:, :, :, :]

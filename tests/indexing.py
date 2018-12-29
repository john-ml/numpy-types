from nptyping import *
import numpy as np

a = np.zeros((3, 4, 5, 6))
b = a[0, :, 3:4]
c = b + np.zeros((1, 2))

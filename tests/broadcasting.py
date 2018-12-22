from nptyping import *
import numpy as np

def f() -> None:
    a = np.zeros((3, 4))
    b = np.zeros(a.shape[0] + 1)
    d = b + np.zeros(1 + a.shape[1])


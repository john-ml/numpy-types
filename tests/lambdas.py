from nptyping import *
import numpy as np

def plus(a: int, b: int) -> a + b:
    return a + b

flip = lambda f: lambda a: lambda b: f(b)(a)
curry = lambda f: lambda a: lambda b: f(a, b)

def test(a: int, b: int) -> None:
    ab = flip(curry)(a)(plus)(b)
    result = np.zeros(ab) + np.zeros(3)

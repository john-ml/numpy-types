from nptyping import *
import numpy as np

def app(f: Fun(a, b), x: a) -> b:
    return f(x)

def compose(f: Fun(b, c), g: Fun(a, b)) -> Fun(a, c):
    def result(x: a) -> c:
        return f(app(g, x))
    return result

def flip(f: Fun(a, Fun(b, c))) -> Fun(b, Fun(a, c)):
    def g(x: b) -> Fun(a, c):
        def h(y: a) -> c:
            return f(y)(x)
        return h
    return g

def curry(f: Fun((a, b), c)) -> Fun(a, Fun(b, c)):
    def g(x: a) -> Fun(b, c):
        def h(y: b) -> c:
            return f(x, y)
        return h
    return g

def const(x: a) -> Fun(b, a):
    def f(_: b) -> a:
        return x
    return f

def plus(a: int, b: int) -> a + b:
    return a + b

def test(a: int, b: int) -> None:
    add = curry(plus)
    app_c = curry(app)
    three = app(app_c(add)(a), b)

    # Unsatisfiable constraint: ForAll([a, b], Implies(True, And(a + b == 3)))
    result = np.zeros(three) + np.zeros(3)

    print(result)

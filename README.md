# Static types for numpy

## Usage

For now, adding
```py
from tests.nptyping import *
```
allows you to write reasonable-enough annotations for function definitions (though it's pretty hacky).

For example:
```py
from tests.nptyping import *
import numpy as np

def f(p: bool, n: int) -> array[n + 2]:
    if p:
        n = 1 + n
        r = np.zeros(n)
    else:
        r = np.zeros(n + 1)
    return np.ones(r.shape[0] + 1) + np.zeros(n + 1 if p else n + 2)
```

`python3 npcheck.py <filename>` to check a file.

## Custom typechecking rules

The typechecker is written so that users can define custom typechecking rules.
A `typerule` decorator provides some syntactic sugar to make this easier.

e.g. to extend the type checker with rule
```
i : nat, a : array (l : list nat), i < len(l) |- a.shape[i] = l[i]
```

can write
```py
@typerule(globals())
def analyze_shape_i(self, context, array, index):
    context, array_type <- self.analyze([context], array)
    if type(array_type) is not Array:
        raise UnificationError(a, Array([AVar(UVar('a'))]), 'expected array type')
    index = index.n
    if index < len(array_type):
        return [(context, array_type[index])]
    else:
        raise ValueError(f'index {index} out of range of dimensions {array_type}')

shape_i = Rule('_array.shape[index__Num]', analyze_shape_i)
```

## Misc. examples

### Broadcasting
```py
a = np.zeros((3, 4,))
b = np.ones(2)

# Can't unify 'array[3, 4]' with 'array[2]' (unbroadcastable dimensions)
c = a + b

d = np.zeros((8, 1, 6, 1))
e = np.ones((7, 1, 5))
f = d * e # OK. i: array[8, 7, 6, 5]

# Can't unify 'array[8, 7, 6]' with 'array[8, 7, 6, 5]' (unbroadcastable dimensions)
g = np.zeros((8, 7, 6)) + f
```

### Inference for lambda expressions

```py
flip = lambda f: lambda a: lambda b: f(b)(a)
# ==> flip : Fun(Fun(a, Fun(b, c)), Fun(b, Fun(a, c)))

curry = lambda f: lambda a: lambda b: f(a, b)
# ==> curry : Fun(Fun((a, b), c), Fun(a, Fun(b, c)))

def plus(a: int, b: int) -> a + b:
    return a + b

def test(a: int, b: int) -> None:
    # ab = a + b
    ab = flip(curry)(a)(plus)(b)
    # Unsatisfiable constraint: ForAll([a, b], Implies(And(True), And(True, a + b == 3)))
    result = np.zeros(ab) + np.zeros(3)
```

### Existential types

```py
# a nontrivial operation (unique, where, etc). _b is existential
def magic(p: bool, x: array[a]) -> array[_b]:
    return np.zeros(3) if p else np.zeros(4) # callee chooses b

# not possible: caller sees (_ : array[b]) + (_ : array[b'])
a = magic(True, np.zeros(1)) + magic(True, np.zeros(2))
# Unsatisfiable constraint: ForAll([_18, _24],
#        And(Implies(True, And(And(_18 == _24), True)),
#            Implies(True, And(And(_18 == _24), True))))
```

More examples in [tests](https://github.com/johnli0135/numpy-types/tree/master/tests).

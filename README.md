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
A `callback` decorator provides some syntactic sugar to make this easier.

For example, the following code defines a rule which essentially checks that the `+` operator has type `forall a. a -> a -> a`:

```py
@callbacks(globals())
def analyze_plus(self, context, lhs, rhs):
    context, lhs_type <- self.analyze([context], lhs)
    context, rhs_type <- self.analyze([context], rhs)
    context.unify(lhs_type, rhs_type)
    return [(context, lhs_type)]
plus = Rule('_lhs + rhs', analyze_plus, 'plus')
```

## Some examples

### Type inference for lambda expressions

```py
flip = lambda f: lambda a: lambda b: f(b)(a)
# ==> flip : Fun(Fun(a, Fun(b, c)), Fun(b, Fun(a, c)))

curry = lambda f: lambda a: lambda b: f(a, b)
# ==> curry : Fun(Fun((a, b), c), Fun(a, Fun(b, c)))

def plus(a: int, b: int) -> a + b:
    return a + b

def test(a: int, b: int) -> None:
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
```

More examples in [tests](https://github.com/johnli0135/numpy-types/tree/master/tests).

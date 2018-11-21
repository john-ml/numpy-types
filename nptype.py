import substitution
import z3

# infinite stream of fresh identifiers
def make_fresh():
    i = 0
    while True:
        yield str(i)
        i += 1
fresh_ids = make_fresh()
del make_fresh

class Type:
    def __str__(self):
        pass
    def __eq__(self, other):
        pass
    def __hash__(self):
        pass
    def tvars(self):
        pass
    def evars(self):
        pass
    def vars(self):
        return self.tvars() | self.evars()
    def rename(self, renamings):
        pass
    def under(self, σ):
        pass
    def to_z3(self):
        return True
    def fresh(self):
        return self.rename(dict(zip((a.name for a in self.vars()), fresh_ids)))
    def flip(self):
        pass

    # for arithmetic expressions
    def __add__(self, other):
        return Add(self, Type.lift(other, context=int))
    def __radd__(self, other):
        return Add(Type.lift(other, context=int), self)
    def __mul__(self, other):
        return Mul(self, Type.lift(other, context=int))
    def __rmul__(self, other):
        return Mul(Type.lift(other, context=int), self)

    # for boolean expressions
    def __or__(self, other):
        return Or(self, Type.lift(other, context=bool))
    def __ror__(self, other):
        return Or(Type.lift(other, context=bool), self)
    def __and__(self, other):
        return And(self, Type.lift(other, context=bool))
    def __rand__(self, other):
        return And(Type.lift(other, context=bool), self)

    @staticmethod
    def lift(a, context=type):
        return ALit(a) if type(a) is int else \
               BLit(a) if type(a) is bool else \
               (EVar(a, context=context) if a.startswith('?') else TVar(a, context=context)) \
                   if type(a) is str else \
               a

# -------------------- variables --------------------

# universal (rigid) type variable
class TVar(Type):
    def __init__(self, name, context=type):
        self.name = name
        self.context = context
    def __str__(self):
        try:
            int(self.name)
        except ValueError:
            return str(self.name)
        return 'tmp' + self.name
    def __eq__(self, other):
        return type(self) is type(other) and self.name == other.name
    def __hash__(self):
        return hash(('TVar', self.name))
    def tvars(self):
        return {self}
    def evars(self):
        return set()
    def rename(self, renamings):
        return TVar(renamings[self.name]) if self.name in renamings else TVar(self.name)
    def under(self, σ):
        return σ.find(self)
    def to_z3(self):
        return z3.Int(self.name) if self.context == int else \
               z3.Bool(self.name) if self.context == bool else \
               z3.Int(self.name) # shrug
    def flip(self):
        return EVar(self.name, context = self.context)

# existential (ambiguous) type variable
class EVar(Type):
    def __init__(self, name, context=type):
        self.name = name
        self.context = context
    def __str__(self):
        try:
            int(self.name)
        except ValueError:
            return '?' + str(self.name)
        return '?tmp' + self.name
    def __eq__(self, other):
        return type(self) is type(other) and self.name == other.name
    def __hash__(self):
        return hash(('EVar', self.name))
    def tvars(self):
        return set()
    def evars(self):
        return {self}
    def rename(self, renamings):
        return EVar(renamings[self.name]) if self.name in renamings else EVar(self.name)
    def under(self, σ):
        return σ.find(self)
    def to_z3(self):
        return z3.Int(self.name) if self.context == int else \
               z3.Bool(self.name) if self.context == bool else \
               z3.Int(self.name) # shrug
    def flip(self):
        return TVar(self.name, context = self.context)

# -------------------- arithmetic expressions --------------------

class AExp(Type):
    def to_z3(self):
        pass

class ALit(AExp):
    def __init__(self, n):
        self.n = n
    def __str__(self):
        return str(self.n)
    def __eq__(self, other):
        return type(self) is type(other) and self.n == other.n
    def __hash__(self):
        return hash(('ALit', self.n))
    def tvars(self):
        return set()
    def evars(self):
        return set()
    def rename(self, renamings):
        return self
    def under(self, σ):
        return self
    def to_z3(self):
        return self.n
    def flip(self):
        return self

class Add(AExp):
    def __init__(self, a, b):
        self.a = a
        self.b = b
    def __str__(self):
        return '{} + {}'.format(str(self.a), str(self.b))
    def __eq__(self, other):
        return type(self) is type(other) and self.a == other.a and self.b == other.b
    def __hash__(self):
        return hash(('Add', self.a, self.b))
    def tvars(self):
        return self.a.tvars() | self.b.tvars()
    def evars(self):
        return self.a.evars() | self.b.evars()
    def rename(self, renamings):
        return Add(self.a.rename(renamings), self.b.rename(renamings))
    def under(self, σ):
        return Add(self.a.under(σ), self.b.under(σ))
    def to_z3(self):
        return self.a.to_z3() + self.b.to_z3()
    def flip(self):
        return Add(self.a.flip(), self.b.flip())

class Mul(AExp):
    def __init__(self, a, b):
        self.a = a
        self.b = b
    def __str__(self):
        return '{} * {}'.format(str(self.a), str(self.b))
    def __eq__(self, other):
        return type(self) is type(other) and self.a == other.a and self.b == other.b
    def __hash__(self):
        return hash(('Mul', self.a, self.b))
    def tvars(self):
        return self.a.tvars() | self.b.tvars()
    def evars(self):
        return self.a.evars() | self.b.evars()
    def rename(self, renamings):
        return Mul(self.a.rename(renamings), self.b.rename(renamings))
    def under(self, σ):
        return Mul(self.a.under(σ), self.b.under(σ))
    def to_z3(self):
        return self.a.to_z3() * self.b.to_z3()
    def flip(self):
        return Mul(self.a.flip(), self.b.flip())

# -------------------- boolean expressions --------------------

class BExp(Type):
    def to_z3(self):
        pass

class BLit(BExp):
    def __init__(self, p):
        self.p = n
    def __str__(self):
        return str(self.p)
    def __eq__(self, other):
        return type(self) is type(other) and self.p == other.n
    def __hash__(self):
        return hash(('BLit', self.p))
    def tvars(self):
        return set()
    def evars(self):
        return set()
    def rename(self, renamings):
        return self
    def under(self, σ):
        return self
    def to_z3(self):
        return self.p
    def flip(self):
        return self

class Or(BExp):
    def __init__(self, a, b):
        self.a = a
        self.b = b
    def __str__(self):
        return '{} ∨ {}'.format(str(self.a), str(self.b))
    def __eq__(self, other):
        return type(self) is type(other) and self.a == other.a and self.b == other.b
    def __hash__(self):
        return hash(('Or', self.a, self.b))
    def tvars(self):
        return self.a.tvars() | self.b.tvars()
    def evars(self):
        return self.a.evars() | self.b.evars()
    def rename(self, renamings):
        return Or(self.a.rename(renamings), self.b.rename(renamings))
    def under(self, σ):
        return Or(self.a.under(σ), self.b.under(σ))
    def to_z3(self):
        return z3.Or(self.a.to_z3(), self.b.to_z3())
    def flip(self):
        return Or(self.a.flip(), self.b.flip())

class And(BExp):
    def __init__(self, a, b):
        self.a = a
        self.b = b
    def __str__(self):
        return '{} ∧ {}'.format(str(self.a), str(self.b))
    def __eq__(self, other):
        return type(self) is type(other) and self.a == other.a and self.b == other.b
    def __hash__(self):
        return hash(('And', self.a, self.b))
    def tvars(self):
        return self.a.tvars() | self.b.tvars()
    def evars(self):
        return self.a.evars() | self.b.evars()
    def rename(self, renamings):
        return And(self.a.rename(renamings), self.b.rename(renamings))
    def under(self, σ):
        return And(self.a.under(σ), self.b.under(σ))
    def to_z3(self):
        return z3.And(self.a.to_z3(), self.b.to_z3())
    def flip(self):
        return And(self.a.flip(), self.b.flip())

# -------------------- numpy array --------------------

class Array(Type):
    def __init__(self, shape):
        self.shape = [Type.lift(a) for a in shape]
    def __str__(self):
        return 'array[{}]'.format(', '.join(str(d) for d in self.shape))
    def __eq__(self, other):
        return type(self) is type(other) and self.shape == other.shape
    def __hash__(self):
        return hash(('Array', tuple(self.shape)))
    def tvars(self):
        from functools import reduce
        return reduce(lambda a, b: a | b, (a.tvars() for a in self.shape))
    def evars(self):
        from functools import reduce
        return reduce(lambda a, b: a | b, (a.evars() for a in self.shape))
    def rename(self, renamings):
        return Array(a.rename(renamings) for a in self.shape)
    def under(self, σ):
        return Array(a.under(σ) for a in self.shape)
    def flip(self):
        return Array(a.flip() for a in self.shape)

# -------------------- unification --------------------

# for Substitution
def compare(a, b):
    return (type(a) is not EVar and type(b) is EVar) or \
           (type(a) is type(b) is EVar and a.name <= b.name)

# update σ : Substitution to unify a and b or fail with ValueError
# return pointer to σ
def unify(a, b, σ):
    cant_unify = lambda a, b, reason='': \
        ValueError("Can't unify '{}' with '{}'{}".format( \
            a, b, ('' if reason == '' else ' ({})'.format(reason))))

    a = a.under(σ)
    b = b.under(σ)

    if isinstance(a, AExp) and isinstance(b, AExp):
        return σ.union(a, b)

    if isinstance(a, BExp) and isinstance(b, BExp):
        return σ.union(a, b)

    if EVar in (type(a), type(b)):
        return σ.union(a, b)

    if type(a) is not type(b):
        raise cant_unify(a, b, 'incompatible types')

    if type(a) is TVar and a != b:
        raise cant_unify(a, b, 'two rigid type variables')

    if type(a) is Array:
        if len(a.shape) != len(b.shape):
            raise cant_unify(a, b, 'shapes are of unequal length')
        for l, r in zip(a.shape, b.shape):
            unify(l, r, σ)
        return σ

    return σ

# --------------------------------------------------------------------------------

if __name__ == '__main__':
    print(Array(['b', TVar('a') + 1]))
    print(isinstance(EVar('b'), AExp), isinstance(EVar('b'), AExp))

    t = Array([1 + TVar('g'), EVar('c') * TVar('a')])
    print([str(a) for a in t.tvars()])
    print([str(a) for a in t.evars()])
    print([str(a) for a in t.vars()])

    t = TVar('g') * 3 + 4 + TVar('a') * EVar('b')
    print(t.to_z3())
    print([str(a) for a in t.evars()])
    print([str(a) for a in t.tvars()])

    print(t.fresh())
    print(t.fresh().flip())

    def try_unify(*args):
        try:
            print(unify(*args))
        except ValueError as e:
            print(e)

    σ = substitution.Substitution(compare)
    try_unify(TVar('a'), TVar('b'), σ)
    try_unify(TVar('a'), TVar('a'), σ)
    try_unify(Array([TVar('a')]), Array([EVar('b')]), σ)
    try_unify(TVar('c'), EVar('d'), σ)
    try_unify(Array([TVar('e')]), Array([TVar('f')]), σ)
    try_unify(Array([1 + TVar('g')]), Array([TVar('g') + 1]), σ)
    try_unify(
        TVar('h', context=bool) & TVar('i', context=bool),
        TVar('i', context=bool) & TVar('h', context=bool), σ)
    
    F = σ.to_z3()
    print(F)
    print(z3.simplify(F))
    s = z3.Solver()
    s.add(F)
    print(s.check() == z3.sat)

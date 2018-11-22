import substitution as S
import util as U
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
    def renamed(self, renamings):
        pass
    def under(self, σ):
        pass
    def to_z3(self):
        return True
    def fresh(self):
        return self.renamed(dict(zip((a.name for a in self.vars()), fresh_ids)))
    def flipped(self):
        pass
    # partial ordering of types, for unification
    def __lshift__(a, b):
        return (type(a) is not EVar and type(b) is EVar) or \
               (type(a) is type(b) is EVar and a.name <= b.name)

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
        if type(a) is int:
            return ALit(a)
        if type(a) is bool:
            return BLit(a)
        if type(a) is str:
            var = EVar(a) if a.startswith('?') else TVar(a)
            if context is type:
                return var
            if context is int:
                return AVar(var)
            if context is bool:
                return BVar(var)
        return a

# -------------------- variables --------------------

# universal (rigid) type variable
class TVar(Type):
    def __init__(self, name):
        self.name = name
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
    def renamed(self, renamings):
        return TVar(renamings[self.name]) if self.name in renamings else TVar(self.name)
    def under(self, σ):
        return σ.find(self)
    def to_z3(self, context=type):
        return z3.Int(self.name) if context == int else \
               z3.Bool(self.name) if context == bool else \
               z3.Int(self.name) # shrug
    def flipped(self):
        return EVar(self.name)

# existential (ambiguous) type variable
class EVar(Type):
    def __init__(self, name):
        self.name = name
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
    def renamed(self, renamings):
        return EVar(renamings[self.name]) if self.name in renamings else EVar(self.name)
    def under(self, σ):
        return σ.find(self)
    def to_z3(self, context=type):
        return z3.Int(self.name) if context == int else \
               z3.Bool(self.name) if context == bool else \
               z3.Int(self.name) # shrug
    def flipped(self):
        return TVar(self.name)

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
    def renamed(self, renamings):
        return self
    def under(self, σ):
        return self
    def to_z3(self):
        return self.n
    def flipped(self):
        return self

class AVar(AExp):
    def __init__(self, var):
        self.var = var
    def __str__(self):
        return '({} : int)'.format(self.var)
    def __eq__(self, other):
        return type(self) is type(other) and self.var == other.var
    def __hash__(self):
        return hash(('AVar', self.var))
    def tvars(self):
        return self.var.tvars()
    def evars(self):
        return self.var.evars()
    def renamed(self, renamings):
        return AVar(self.var.renamed(renamings))
    def under(self, σ):
        return AVar(self.var.under(σ))
    def to_z3(self):
        return self.var.to_z3(context=int)
    def flipped(self):
        return AVar(self.var.flipped())

class Add(AExp):
    def __init__(self, a, b):
        self.a = a
        self.b = b
    def __str__(self):
        return '{} + {}'.format(self.a, self.b)
    def __eq__(self, other):
        return type(self) is type(other) and self.a == other.a and self.b == other.b
    def __hash__(self):
        return hash(('Add', self.a, self.b))
    def tvars(self):
        return self.a.tvars() | self.b.tvars()
    def evars(self):
        return self.a.evars() | self.b.evars()
    def renamed(self, renamings):
        return Add(self.a.renamed(renamings), self.b.renamed(renamings))
    def under(self, σ):
        return Add(self.a.under(σ), self.b.under(σ))
    def to_z3(self):
        return self.a.to_z3() + self.b.to_z3()
    def flipped(self):
        return Add(self.a.flipped(), self.b.flipped())

class Mul(AExp):
    def __init__(self, a, b):
        self.a = a
        self.b = b
    def __str__(self):
        return '{} * {}'.format(self.a, self.b)
    def __eq__(self, other):
        return type(self) is type(other) and self.a == other.a and self.b == other.b
    def __hash__(self):
        return hash(('Mul', self.a, self.b))
    def tvars(self):
        return self.a.tvars() | self.b.tvars()
    def evars(self):
        return self.a.evars() | self.b.evars()
    def renamed(self, renamings):
        return Mul(self.a.renamed(renamings), self.b.renamed(renamings))
    def under(self, σ):
        return Mul(self.a.under(σ), self.b.under(σ))
    def to_z3(self):
        return self.a.to_z3() * self.b.to_z3()
    def flipped(self):
        return Mul(self.a.flipped(), self.b.flipped())

# -------------------- boolean expressions --------------------

class BExp(Type):
    def to_z3(self):
        pass

class BLit(BExp):
    def __init__(self, p):
        self.p = p
    def __str__(self):
        return str(self.p)
    def __eq__(self, other):
        return type(self) is type(other) and self.p == other.p
    def __hash__(self):
        return hash(('BLit', self.p))
    def tvars(self):
        return set()
    def evars(self):
        return set()
    def renamed(self, renamings):
        return self
    def under(self, σ):
        return self
    def to_z3(self):
        return self.p
    def flipped(self):
        return self

class BVar(AExp):
    def __init__(self, var):
        self.var = var
    def __str__(self):
        return '({} : bool)'.format(self.var)
    def __eq__(self, other):
        return type(self) is type(other) and self.var == other.var
    def __hash__(self):
        return hash(('BVar', self.var))
    def tvars(self):
        return self.var.tvars()
    def evars(self):
        return self.var.evars()
    def renamed(self, renamings):
        return BVar(self.var.renamed(renamings))
    def under(self, σ):
        return BVar(self.var.under(σ))
    def to_z3(self):
        return self.var.to_z3(context=bool)
    def flipped(self):
        return BVar(self.var.flipped())

class Or(BExp):
    def __init__(self, a, b):
        self.a = a
        self.b = b
    def __str__(self):
        return '{} ∨ {}'.format(self.a, self.b)
    def __eq__(self, other):
        return type(self) is type(other) and self.a == other.a and self.b == other.b
    def __hash__(self):
        return hash(('Or', self.a, self.b))
    def tvars(self):
        return self.a.tvars() | self.b.tvars()
    def evars(self):
        return self.a.evars() | self.b.evars()
    def renamed(self, renamings):
        return Or(self.a.renamed(renamings), self.b.renamed(renamings))
    def under(self, σ):
        return Or(self.a.under(σ), self.b.under(σ))
    def to_z3(self):
        return z3.Or(self.a.to_z3(), self.b.to_z3())
    def flipped(self):
        return Or(self.a.flipped(), self.b.flipped())

class And(BExp):
    def __init__(self, a, b):
        self.a = a
        self.b = b
    def __str__(self):
        return '{} ∧ {}'.format(self.a, self.b)
    def __eq__(self, other):
        return type(self) is type(other) and self.a == other.a and self.b == other.b
    def __hash__(self):
        return hash(('And', self.a, self.b))
    def tvars(self):
        return self.a.tvars() | self.b.tvars()
    def evars(self):
        return self.a.evars() | self.b.evars()
    def renamed(self, renamings):
        return And(self.a.renamed(renamings), self.b.renamed(renamings))
    def under(self, σ):
        return And(self.a.under(σ), self.b.under(σ))
    def to_z3(self):
        return z3.And(self.a.to_z3(), self.b.to_z3())
    def flipped(self):
        return And(self.a.flipped(), self.b.flipped())

class Not(BExp):
    def __init__(self, a):
        self.a = a
    def __str__(self):
        return '¬{}'.format(self.a)
    def __eq__(self, other):
        return type(self) is type(other) and self.a == other.a
    def __hash__(self):
        return hash(('Not', self.a))
    def tvars(self):
        return self.a.tvars()
    def evars(self):
        return self.a.evars()
    def renamed(self, renamings):
        return Not(self.a.renamed(renamings))
    def under(self, σ):
        return Not(self.a.under(σ))
    def to_z3(self):
        return z3.Not(self.a.to_z3())
    def flipped(self):
        return Not(self.a.flipped())

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
    def renamed(self, renamings):
        return Array(a.renamed(renamings) for a in self.shape)
    def under(self, σ):
        return Array(a.under(σ) for a in self.shape)
    def flipped(self):
        return Array(a.flipped() for a in self.shape)

# -------------------- unification --------------------

# update σ : Substitution ∪ Context to unify a and b or fail with ValueError
# return pointer to σ
def unify(a, b, σ):
    cant_unify = lambda a, b, reason='': \
        ValueError("Can't unify '{}' with '{}'{}".format( \
            a, b, ('' if reason == '' else ' ({})'.format(reason))))

    a = a.under(σ)
    b = b.under(σ)

    # existential variables always unify
    if EVar in (type(a), type(b)):
        return σ.union(a, b)

    # lifted variables
    elif type(a) is type(b) is AVar or type(a) is type(b) is BVar:
        return unify(a.var, b.var, σ)

    # defer arithmetic or boolean expressions to z3
    elif isinstance(a, AExp) and isinstance(b, AExp) or \
         isinstance(a, BExp) and isinstance(b, BExp):
        return σ.union(a, b)

    elif type(a) is not type(b):
        raise cant_unify(a, b, 'incompatible types')

    elif type(a) is TVar and a != b:
        raise cant_unify(a, b, 'two rigid type variables')

    elif type(a) is Array:
        if len(a.shape) != len(b.shape):
            raise cant_unify(a, b, 'shapes are of unequal length')
        for l, r in zip(a.shape, b.shape):
            print(l, r)
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
    print(t.fresh().flipped())

    def try_unify(*args):
        try:
            print(unify(*args))
        except ValueError as e:
            print(e)

    σ = S.Substitution(lambda a, b: a << b)
    try_unify(TVar('a'), TVar('b'), σ)
    try_unify(TVar('a'), TVar('a'), σ)
    try_unify(Array([AVar(TVar('a'))]), Array([AVar(EVar('b'))]), σ)
    try_unify(AVar(TVar('c')), AVar(EVar('d')), σ)
    try_unify(Array([AVar(TVar('e'))]), Array([AVar(TVar('f'))]), σ)
    try_unify(Array([1 + AVar(TVar('g'))]), Array([AVar(TVar('g')) + 1]), σ)
    try_unify(
        BVar(TVar('h')) & BVar(TVar('i')),
        BVar(TVar('i')) & BVar(TVar('h')), σ)
    
    F = σ.to_z3()
    print(F)
    print(σ.evars(), σ.tvars())
    print(z3.simplify(F))
    s = z3.Solver()
    F = z3.ForAll(σ.tvars(), z3.Exists(σ.evars(), F))
    print(F)
    s.add(F)
    print(s.check() == z3.sat)

    s1 = z3.Solver()
    F1 = U.to_quantified_z3(σ)
    print(F1)

import util as U
import pattern as P
import ast as A
import substitution as S
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
    def fresh_all(types):
        renaming = dict(zip(v.name for t in types for v in t.vars()), fresh_ids)
        return [t.renamed(renaming) for t in types]

    @staticmethod
    def lift(a, context=type):
        if a is None:
            return TNone()
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

# -------------------- none --------------------

class TNone(Type):
    def __init__(self):
        pass
    def __str__(self):
        return 'None'
    def __eq__(self, other):
        return type(other) is TNone
    def __hash__(self):
        return hash('TNone')
    def tvars(self):
        return set()
    def evars(self):
        return set()
    def renamed(self, renamings):
        return self
    def under(self, σ):
        return self
    def to_z3(self, context=type):
        return z3.Int(next(fresh_ids)) # TODO: replace with something reasonable
    def flipped(self):
        return self

# -------------------- arithmetic expressions --------------------

class AExp(Type):
    def to_z3(self):
        pass

class ALit(AExp):
    def __init__(self, n):
        self.value = n
    def __str__(self):
        return str(self.value)
    def __eq__(self, other):
        return type(self) is type(other) and self.value == other.value
    def __hash__(self):
        return hash(('ALit', self.value))
    def tvars(self):
        return set()
    def evars(self):
        return set()
    def renamed(self, renamings):
        return self
    def under(self, σ):
        return self
    def to_z3(self):
        return self.value
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
        return σ.find(self)
    def to_z3(self):
        return self.var.to_z3(context=int)
    def flipped(self):
        return AVar(self.var.flipped())

class Add(AExp):
    def __init__(self, a, b):
        self.a = a
        self.b = b
    def __str__(self):
        return '({} + {})'.format(self.a, self.b)
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
        return '({} * {})'.format(self.a, self.b)
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
        self.value = p
    def __str__(self):
        return str(self.value)
    def __eq__(self, other):
        return type(self) is type(other) and self.value == other.value
    def __hash__(self):
        return hash(('BLit', self.value))
    def tvars(self):
        return set()
    def evars(self):
        return set()
    def renamed(self, renamings):
        return self
    def under(self, σ):
        return self
    def to_z3(self):
        return self.value
    def flipped(self):
        return self

class BVar(BExp):
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
        return σ.find(self)
    def to_z3(self):
        return self.var.to_z3(context=bool)
    def flipped(self):
        return BVar(self.var.flipped())

class Or(BExp):
    def __init__(self, a, b):
        self.a = a
        self.b = b
    def __str__(self):
        return '({} ∨ {})'.format(self.a, self.b)
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
        return '({} ∧ {})'.format(self.a, self.b)
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

# -------------------- compound types --------------------

# tuple
class Tuple(Type):
    def __init__(self, items):
        self.items = [Type.lift(a) for a in items]
    def __str__(self):
        return '({})'.format(', '.join(str(d) for d in self.items))
    def __eq__(self, other):
        return type(self) is type(other) and self.items == other.items
    def __len__(self):
        return len(self.items)
    def __iter__(self):
        return (a for a in self.items)
    def __hash__(self):
        return hash(('Tuple', tuple(self.items)))
    def tvars(self):
        return U.mapreduce(U.union, U.tvars, self.items, set())
    def evars(self):
        return U.mapreduce(U.union, U.evars, self.items, set())
    def renamed(self, renamings):
        return Tuple(a.renamed(renamings) for a in self.items)
    def under(self, σ):
        return Tuple(a.under(σ) for a in self.items)
    def flipped(self):
        return Tuple(a.flipped() for a in self.items)

# numpy array
class Array(Type):
    def __init__(self, shape):
        self.shape = [Type.lift(a) for a in shape]
    def __str__(self):
        return 'array[{}]'.format(', '.join(str(d) for d in self.shape))
    def __eq__(self, other):
        return type(self) is type(other) and self.shape == other.shape
    def __len__(self):
        return len(self.shape)
    def __iter__(self):
        return (a for a in self.shape)
    def __hash__(self):
        return hash(('Array', tuple(self.shape)))
    def tvars(self):
        return U.mapreduce(U.union, U.tvars, self.shape, set())
    def evars(self):
        return U.mapreduce(U.union, U.evars, self.shape, set())
    def renamed(self, renamings):
        return Array(a.renamed(renamings) for a in self.shape)
    def under(self, σ):
        return Array(a.under(σ) for a in self.shape)
    def flipped(self):
        return Array(a.flipped() for a in self.shape)

# function
class Fun(Type):
    def __init__(self, a, b):
        self.a = a
        self.b = b
    def __str__(self):
        return 'Fun({}, {})'.format(self.a, self.b)
    def __eq__(self, other):
        return type(self) is type(other) and self.a == other.a and self.b == other.b
    def __hash__(self):
        return hash(('Fun', self.a, self.b))
    def tvars(self):
        return self.a.tvars() | self.b.tvars()
    def evars(self):
        return self.a.evars() | self.b.evars()
    def renamed(self, renamings):
        return Fun(self.a.renamed(renamings), self.b.renamed(renamings))
    def under(self, σ):
        return Fun(self.a.under(σ), self.b.under(σ))
    def flipped(self):
        return Fun(self.a.flipped(), self.b.flipped())

# -------------------- unification --------------------

# update σ : Substitution ∪ Context to unify a and b or fail with ValueError
# return pointer to σ
def unify(a, b, σ):
    a = a.under(σ)
    b = b.under(σ)

    # existential variables
    if EVar in (type(a), type(b)):
        e, t = (a, b) if type(a) is EVar else (b, a)
        if e in t.evars():
            raise U.cant_unify(a, b, 'occurs check failed')
        return σ.union(a, b)

    # lifted variables
    elif type(a) is type(b) is AVar or type(a) is type(b) is BVar:
        return unify(a.var, b.var, σ)

    # literals
    elif type(a) is type(b) is ALit or type(a) is type(b) is BLit:
        if a.value != b.value:
            raise U.cant_unify(a, b, 'unequal values')
        return σ

    # defer arithmetic or boolean expressions to z3
    elif isinstance(a, AExp) and isinstance(b, AExp) or \
         isinstance(a, BExp) and isinstance(b, BExp):
        return σ.union(a, b)

    elif type(a) is not type(b):
        raise U.cant_unify(a, b, 'incompatible types')

    elif type(a) is TVar and a != b:
        raise U.cant_unify(a, b, 'two rigid type variables')

    elif type(a) is Fun:
        return unify(a.a, b.a, unify(a.b, b.b, σ))

    elif type(a) in (Array, Tuple):
        if len(a) != len(b):
            raise U.cant_unify(a, b, 'unequal lengths')
        for l, r in zip(a, b):
            unify(l, r, σ)
        return σ

    return σ

def parse(s):
    name2var = lambda name: (EVar(name.id[1:]) if name.id[0] == '_' else TVar(name.id))
    rules = [
        ('a__Num', lambda a: ALit(a.n)),

        ('a__Name + b__Name', lambda a, b: Add(AVar(name2var(a)), AVar(name2var(b)))),
        ('a__Name + _b', lambda a, b: Add(AVar(name2var(a)), go(b))),
        ('_a + b__Name', lambda a, b: Add(go(a), AVar(name2var(b)))),
        ('_a + _b', lambda a, b: Add(go(a), go(b))),

        ('a__Name * b__Name', lambda a, b: Mul(AVar(name2var(a)), AVar(name2var(b)))),
        ('a__Name * _b', lambda a, b: Mul(AVar(name2var(a)), go(b))),
        ('_a * b__Name', lambda a, b: Mul(go(a), AVar(name2var(b)))),
        ('_a * _b', lambda a, b: Mul(go(a), go(b))),

        ('a__Name and b__Name', lambda a, b: And(BVar(name2var(a)), BVar(name2var(b)))),
        ('a__Name and _b', lambda a, b: And(BVar(name2var(a)), go(b))),
        ('_a and b__Name', lambda a, b: And(go(a), BVar(name2var(b)))),
        ('_a and _b', lambda a, b: And(go(a), go(b))),

        ('a__Name or b__Name', lambda a, b: Or(BVar(name2var(a)), BVar(name2var(b)))),
        ('a__Name or _b', lambda a, b: Or(BVar(name2var(a)), go(b))),
        ('_a or b__Name', lambda a, b: Or(go(a), BVar(name2var(b)))),
        ('_a or _b', lambda a, b: Or(go(a), go(b))),

        ('not a__Name', lambda a: Not(BVar(name2var(a)))),
        ('not _a', lambda a: Not(go(a))),

        ('a__Name', lambda a: name2var(a)),
        ('int(a__Name)', lambda a: AVar(name2var(a))),
        ('bool(a__Name)', lambda a: BVar(name2var(a))),

        ('Fun(_a, _b)', lambda a, b: Fun(go(a), go(b))),
        ('array[__a]', lambda a: Array(
            [go(i) for i in a.elts] if type(a) is A.Tuple else
            [go(a)])),
        ('a__Tuple', lambda a: Tuple([go(i) for i in a.elts])),

        ('True', lambda: BLit(True)),
        ('False', lambda: BLit(False))]
    def go(ast):
        for s, action in rules:
            matches = P.matches(P.make_pattern(s), ast)
            if matches is not None:
                return action(**matches)
        else:
            raise ValueError('Failed to parse ast node: ' + P.pretty(P.explode(ast)))

    ast = A.parse(s.replace('?', '_')).body[0].value
    return go(ast)

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

    def try_unify(a, b, σ):
        try:
            print(a, '~', b)
            print(unify(a, b, σ))
        except ValueError as e:
            print(e)
        finally:
            print()

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
    F = U.to_quantified_z3(σ)
    print(F)
    s.add(F)
    print(s.check() == z3.sat)

    print(parse('array[?n + 1 + m*(n+3), 1, 2, True, False, int(?a), bool(a)]'))

    try_unify(parse('?a'), parse('array[?a]'), σ)
    try_unify(parse('?a'), parse('array[b]'), σ)

    try_unify(parse('array[a, b, c]'), parse('array[d]'), σ)
    try_unify(parse('(a, b, c)'), parse('(d, e)'), σ)
    try_unify(parse('Fun(True, False)'), parse('Fun(False, False)'), σ)
    try_unify(parse('Fun(array[n], array[n + 1])'), parse('Fun(array[n], array[1 + n])'), σ)

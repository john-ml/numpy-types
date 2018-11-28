import util as U
import pattern as P
import ast as A
import substitution as S
import z3

class Type:
    def __str__(self):
        pass
    def __eq__(self, other):
        pass
    def __hash__(self):
        pass
    def uvars(self):
        pass
    def evars(self):
        pass
    def vars(self):
        return self.uvars() | self.evars()
    def names(self):
        return {v.name if type(v) in (UVar, EVar) else v.var.name for v in self.vars()}
    def renamed(self, renamings):
        pass
    def under(self, σ):
        pass
    def to_z3(self):
        return True
    def fresh(self, blacklist=None):
        renaming = dict(zip(self.names(), U.fresh_ids))
        if blacklist is not None:
            for a in blacklist:
                renaming[a] = a
        return self.renamed(renaming)
    def eapp(self, blacklist=None):
        pass
    # partial ordering of types, for unification
    def __lshift__(a, b):
        is_e = lambda v, t: type(v) is t and type(v.var) is EVar
        return (type(a) is not EVar and type(b) is EVar or
                type(a) is type(b) is EVar and a.name <= b.name or
                not is_e(a, AVar) and isinstance(a, AExp) and is_e(b, AVar) or
                not is_e(a, BVar) and isinstance(a, BExp) and is_e(b, BVar) or
                is_e(a, AVar) and is_e(b, AVar) and a.var.name <= b.var.name or
                is_e(a, BVar) and is_e(b, BVar) and a.var.name <= b.var.name)

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
        renaming = dict(zip((name for t in types for name in t.names()), U.fresh_ids))
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
            var = EVar(a) if a.startswith('?') else UVar(a)
            if context is type:
                return var
            if context is int:
                return AVar(var)
            if context is bool:
                return BVar(var)
        return a

# -------------------- variables --------------------

# universal (rigid) type variable
class UVar(Type):
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
        return hash(('UVar', self.name))
    def uvars(self):
        return {self}
    def evars(self):
        return set()
    def renamed(self, renamings):
        return UVar(renamings[self.name]) if self.name in renamings else UVar(self.name)
    def under(self, σ):
        return σ.find(self)
    def to_z3(self, context=type):
        return z3.Int(self.name) if context == int else \
               z3.Bool(self.name) if context == bool else \
               z3.Int(self.name) # shrug
    def eapp(self, blacklist=[]):
        return EVar(self.name) if self.name not in blacklist else UVar(self.name)

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
    def uvars(self):
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
    def eapp(self, blacklist=[]):
        return EVar(self.name)

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
    def uvars(self):
        return set()
    def evars(self):
        return set()
    def renamed(self, renamings):
        return self
    def under(self, σ):
        return self
    def to_z3(self, context=type):
        return z3.Int(next(U.fresh_ids)) # TODO: replace with something reasonable
    def eapp(self, blacklist=[]):
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
    def uvars(self):
        return set()
    def evars(self):
        return set()
    def renamed(self, renamings):
        return self
    def under(self, σ):
        return self
    def to_z3(self):
        return self.value
    def eapp(self, blacklist=[]):
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
    def uvars(self):
        return {self} if type(self.var) is UVar else set()
    def evars(self):
        return {self} if type(self.var) is EVar else set()
    def renamed(self, renamings):
        return AVar(self.var.renamed(renamings))
    def under(self, σ):
        return σ.find(self)
    def to_z3(self):
        return self.var.to_z3(context=int)
    def eapp(self, blacklist=[]):
        return AVar(self.var.eapp(blacklist))

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
    def uvars(self):
        return self.a.uvars() | self.b.uvars()
    def evars(self):
        return self.a.evars() | self.b.evars()
    def renamed(self, renamings):
        return Add(self.a.renamed(renamings), self.b.renamed(renamings))
    def under(self, σ):
        return Add(self.a.under(σ), self.b.under(σ))
    def to_z3(self):
        return self.a.to_z3() + self.b.to_z3()
    def eapp(self, blacklist=[]):
        return Add(self.a.eapp(blacklist), self.b.eapp(blacklist))

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
    def uvars(self):
        return self.a.uvars() | self.b.uvars()
    def evars(self):
        return self.a.evars() | self.b.evars()
    def renamed(self, renamings):
        return Mul(self.a.renamed(renamings), self.b.renamed(renamings))
    def under(self, σ):
        return Mul(self.a.under(σ), self.b.under(σ))
    def to_z3(self):
        return self.a.to_z3() * self.b.to_z3()
    def eapp(self, blacklist=[]):
        return Mul(self.a.eapp(blacklist), self.b.eapp(blacklist))

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
    def uvars(self):
        return set()
    def evars(self):
        return set()
    def renamed(self, renamings):
        return self
    def under(self, σ):
        return self
    def to_z3(self):
        return self.value
    def eapp(self, blacklist=[]):
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
    def uvars(self):
        return {self} if type(self.var) is UVar else set()
    def evars(self):
        return {self} if type(self.var) is EVar else set()
    def renamed(self, renamings):
        return BVar(self.var.renamed(renamings))
    def under(self, σ):
        return σ.find(self)
    def to_z3(self):
        return self.var.to_z3(context=bool)
    def eapp(self, blacklist=[]):
        return BVar(self.var.eapp(blacklist))

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
    def uvars(self):
        return self.a.uvars() | self.b.uvars()
    def evars(self):
        return self.a.evars() | self.b.evars()
    def renamed(self, renamings):
        return Or(self.a.renamed(renamings), self.b.renamed(renamings))
    def under(self, σ):
        return Or(self.a.under(σ), self.b.under(σ))
    def to_z3(self):
        return z3.Or(self.a.to_z3(), self.b.to_z3())
    def eapp(self, blacklist=[]):
        return Or(self.a.eapp(blacklist), self.b.eapp(blacklist))

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
    def uvars(self):
        return self.a.uvars() | self.b.uvars()
    def evars(self):
        return self.a.evars() | self.b.evars()
    def renamed(self, renamings):
        return And(self.a.renamed(renamings), self.b.renamed(renamings))
    def under(self, σ):
        return And(self.a.under(σ), self.b.under(σ))
    def to_z3(self):
        return z3.And(self.a.to_z3(), self.b.to_z3())
    def eapp(self, blacklist=[]):
        return And(self.a.eapp(blacklist), self.b.eapp(blacklist))

class Not(BExp):
    def __init__(self, a):
        self.a = a
    def __str__(self):
        return '¬{}'.format(self.a)
    def __eq__(self, other):
        return type(self) is type(other) and self.a == other.a
    def __hash__(self):
        return hash(('Not', self.a))
    def uvars(self):
        return self.a.uvars()
    def evars(self):
        return self.a.evars()
    def renamed(self, renamings):
        return Not(self.a.renamed(renamings))
    def under(self, σ):
        return Not(self.a.under(σ))
    def to_z3(self):
        return z3.Not(self.a.to_z3())
    def eapp(self, blacklist=[]):
        return Not(self.a.eapp(blacklist))

# -------------------- compound types --------------------

# tuple
class Tuple(Type):
    def __init__(self, items):
        self.items = [Type.lift(a) for a in items]
    def __str__(self):
        if len(self.items) == 1:
            return '({},)'.format(self.items[0])
        return '({})'.format(', '.join(str(d) for d in self.items))
    def __eq__(self, other):
        return type(self) is type(other) and self.items == other.items
    def __len__(self):
        return len(self.items)
    def __iter__(self):
        return (a for a in self.items)
    def __hash__(self):
        return hash(('Tuple', tuple(self.items)))
    def uvars(self):
        return U.mapreduce(U.union, U.uvars, self.items, set())
    def evars(self):
        return U.mapreduce(U.union, U.evars, self.items, set())
    def renamed(self, renamings):
        return Tuple(a.renamed(renamings) for a in self.items)
    def under(self, σ):
        return Tuple(a.under(σ) for a in self.items)
    def eapp(self, blacklist=[]):
        return Tuple(a.eapp(blacklist) for a in self.items)

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
    def uvars(self):
        return U.mapreduce(U.union, U.uvars, self.shape, set())
    def evars(self):
        return U.mapreduce(U.union, U.evars, self.shape, set())
    def renamed(self, renamings):
        return Array(a.renamed(renamings) for a in self.shape)
    def under(self, σ):
        return Array(a.under(σ) for a in self.shape)
    def eapp(self, blacklist=[]):
        return Array(a.eapp(blacklist) for a in self.shape)

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
    def uvars(self):
        return self.a.uvars() | self.b.uvars()
    def evars(self):
        return self.a.evars() | self.b.evars()
    def renamed(self, renamings):
        return Fun(self.a.renamed(renamings), self.b.renamed(renamings))
    def under(self, σ):
        return Fun(self.a.under(σ), self.b.under(σ))
    def eapp(self, blacklist=[]):
        return Fun(self.a.eapp(blacklist), self.b.eapp(blacklist))

# -------------------- unification --------------------

class UnificationError(Exception):
    def __init__(self, a, b, reason):
        self.a = a
        self.b = b
        self.reason = reason

    def __str__(self):
        return "Can't unify '{}' with '{}'{}".format( \
            self.a,
            self.b,
            ('' if self.reason == '' else ' ({})'.format(self.reason)))

# update σ : Substitution ∪ Context to unify a and b or fail with ValueError
# return pointer to σ
def unify(a, b, σ):
    a = a.under(σ)
    b = b.under(σ)
    unwrap = lambda t: (t.items[0] if type(t) is Tuple and len(t.items) == 1 else t)
    a = unwrap(a)
    b = unwrap(b)

    # existential variables
    if EVar in (type(a), type(b)):
        e, t = (a, b) if type(a) is EVar else (b, a)
        if e in t.evars() and e != t:
            raise UnificationError(a, b, 'occurs check failed')
        return σ.union(a, b)

    # lifted variables
    elif type(a) is type(b) is AVar or type(a) is type(b) is BVar:
        if EVar in (type(a.var), type(b.var)):
            return σ.union(a, b)
        else:
            assert type(a.var) is type(b.var) is UVar
            if a == b:
                return σ
            raise UnificationError(a, b, 'two rigid type variables')

    # literals
    elif type(a) is type(b) is ALit or type(a) is type(b) is BLit:
        if a.value != b.value:
            raise UnificationError(a, b, 'unequal values')
        return σ

    # defer arithmetic or boolean expressions to z3
    elif isinstance(a, AExp) and isinstance(b, AExp) or \
         isinstance(a, BExp) and isinstance(b, BExp):
        return σ.union(a, b)

    elif type(a) is not type(b):
        raise UnificationError(a, b, 'incompatible types')

    elif type(a) is UVar and a != b:
        raise UnificationError(a, b, 'two rigid type variables')

    elif type(a) is Fun:
        return unify(a.a, b.a, unify(a.b, b.b, σ))

    elif type(a) in (Array, Tuple):
        if len(a) != len(b):
            raise UnificationError(a, b, 'unequal lengths')
        for l, r in zip(a, b):
            unify(l, r, σ)
        return σ

    return σ

# -------------------- parsing --------------------

name2var = lambda name: (EVar(name.id[1:]) if name.id[0] == '_' else UVar(name.id))
to_int = (lambda t:
    AVar(t) if type(t) in (UVar, EVar) else
    t if type(t) in (ALit, AVar) else
    type(t)(to_int(t.a), to_int(t.b)))
to_bool = (lambda t:
    BVar(t) if type(t) in (UVar, EVar) else
    t if type(t) in (BLit, BVar) else
    Not(to_bool(t.a)) if type(t) is Not else
    type(t)(to_bool(t.a), to_bool(t.b)))

def from_ast(ast):
    rules = [
        ('a__Num', lambda a: ALit(a.n)),

        ('_a + _b', lambda a, b: Add(to_int(go(a)), to_int(go(b)))),
        ('_a * _b', lambda a, b: Mul(to_int(go(a)), to_int(go(b)))),

        ('_a : int', lambda a: (a, AVar(UVar(a)))),
        ('_a : bool', lambda a: (a, BVar(UVar(a)))),
        ('_a : _t', lambda a, t: (a, go(t))),

        ('int', lambda: AVar(EVar(next(U.fresh_ids)))),
        ('bool', lambda: BVar(EVar(next(U.fresh_ids)))),
        ('a__Name', lambda a: name2var(a)),

        ('Fun(_a, _b)', lambda a, b: Fun(go(a), go(b))),
        ('array[__a]', lambda a: Array(
            [to_int(go(i)) for i in a.elts] if type(a) is A.Tuple else
            [to_int(go(a))])),
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

    return go(ast)

def parse(s):
    name2var = lambda name: (EVar(name.id[1:]) if name.id[0] == '_' else UVar(name.id))
    rules = [
        ('a__Num', lambda a: ALit(a.n)),

        ('_a + _b', lambda a, b: Add(to_int(go(a)), to_int(go(b)))),
        ('_a * _b', lambda a, b: Mul(to_int(go(a)), to_int(go(b)))),

        ('_a and _b', lambda a, b: And(to_bool(go(a)), to_bool(go(b)))),
        ('_a or _b', lambda a, b: Or(to_bool(go(a)), to_bool(go(b)))),
        ('not _a', lambda a: Not(to_bool(go(a)))),

        ('a__Name', lambda a: name2var(a)),
        ('int(a__Name)', lambda a: AVar(name2var(a))),
        ('bool(a__Name)', lambda a: BVar(name2var(a))),

        ('Fun(_a, _b)', lambda a, b: Fun(go(a), go(b))),
        ('array[__a]', lambda a: Array(
            [to_int(go(i)) for i in a.elts] if type(a) is A.Tuple else
            [to_int(go(a))])),
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
    print(Array(['b', UVar('a') + 1]))
    print(isinstance(EVar('b'), AExp), isinstance(EVar('b'), AExp))

    t = Array([1 + UVar('g'), EVar('c') * UVar('a')])
    print([str(a) for a in t.uvars()])
    print([str(a) for a in t.evars()])
    print([str(a) for a in t.vars()])

    t = UVar('g') * 3 + 4 + UVar('a') * EVar('b')
    print(t.to_z3())
    print([str(a) for a in t.evars()])
    print([str(a) for a in t.uvars()])

    print(t.fresh())
    print(t.fresh().eapp())

    def try_unify(a, b, σ):
        try:
            print(a, '~', b)
            print(unify(a, b, σ))
        except ValueError as e:
            print(e)
        finally:
            print()

    σ = S.Substitution(lambda a, b: a << b)
    try_unify(UVar('a'), UVar('b'), σ)
    try_unify(UVar('a'), UVar('a'), σ)
    try_unify(Array([AVar(UVar('a'))]), Array([AVar(EVar('b'))]), σ)
    try_unify(AVar(UVar('c')), AVar(EVar('d')), σ)
    try_unify(Array([AVar(UVar('e'))]), Array([AVar(UVar('f'))]), σ)
    try_unify(Array([1 + AVar(UVar('g'))]), Array([AVar(UVar('g')) + 1]), σ)
    try_unify(
        BVar(UVar('h')) & BVar(UVar('i')),
        BVar(UVar('i')) & BVar(UVar('h')), σ)
    
    F = σ.to_z3()
    print(F)
    print(σ.evars(), σ.uvars())
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

    arg = P.matches(
        P.make_pattern('def f(__a):\n pass'),
        A.parse('def f(a : int):\n pass').body[0])
    arg = arg['a'][0]
    print(P.pretty(P.explode(arg)))
    print(from_ast(arg), str(from_ast(arg)[1]))

    arg = P.matches(
        P.make_pattern('def f(__a):\n pass'),
        A.parse('def f(a : array[1 + n]):\n pass').body[0])
    arg = arg['a'][0]
    print(P.pretty(P.explode(arg)))
    print(from_ast(arg), str(from_ast(arg)[1]))

    arg = P.matches(
        P.make_pattern('def f() -> _r:\n pass'),
        A.parse('def f() -> array[1 + n]:\n pass').body[0])['r']
    print(P.pretty(P.explode(arg)))
    print(from_ast(arg))

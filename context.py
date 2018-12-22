import util as U
import pattern as P
import nptype as T
import substitution as S
import ast as A

# substitution map + typing environment under some precondition
class Context:
    def __init__(self):
        self.σ = S.Substitution(lambda a, b: a << b)
        self.Γ = {}
        self.F = T.BLit(True)
        self.names = {}
        self.fixed = {}
        self.hash = None
        self.simple = None

    def __str__(self):
        return '{} -> {} ({} fixed) ({})'.format(
            self.F,
            U.typedict(self.Γ),
            '{' + ', '.join(self.fixed) + '}',
            self.σ)

    def __contains__(self, a):
        return a in self.Γ

    def renamed(self, renaming):
        renamed = lambda a: a.renamed(renaming) if hasattr(a, 'under') else a

        c = Context()
        c.σ = S.Substitution(self.σ.compare)
        c.σ.m = dict((renamed(k), renamed(v)) for k, v in self.σ.m.items())
        c.σ.equalities = {(renamed(l), renamed(r)) for l, r in self.σ.equalities}
        c.σ.bias = self.σ.bias
        c.Γ = dict((renamed(k), renamed(v)) for k, v in self.Γ.items())
        c.F = renamed(self.F)
        c.names = {(renaming[a] if a in renaming else a) for a in self.names}
        c.fixed = {(renaming[a] if a in renaming else a) for a in self.names}
        return c

    def reduced(self):
        if self.simple is None:
            self.simple = self.renamed(dict(zip(sorted(self.names), U.make_fresh())))
        return self.simple

    def __hash__(self):
        if self.hash is None:
            simple = self.reduced()
            self.hash = hash((simple.σ, tuple(simple.Γ.items()), simple.F))
        return self.hash

    def __eq__(self, other):
        if type(other) is not Context or hash(self) != hash(other):
            return False
        self = self.reduced()
        other = other.reduced()
        return (self.σ, self.Γ, self.F) == (other.σ, other.Γ, other.F)

    def copy(self):
        c = Context()
        c.σ = self.σ.copy()
        c.Γ = dict(self.Γ)
        c.F = self.F
        c.names = set(self.names)
        c.fixed = set(self.fixed)
        c.hash = self.hash
        c.simple = self.simple
        return c

    def annotate(self, a, t, fixed=False):
        self.Γ[a] = t
        new_names = U.names_of(a) | U.names_of(t)
        self.names |= new_names
        if fixed:
            self.fixed |= new_names
        self.hash = self.simple = None
        return self

    def typeof(self, a):
        if a not in self.Γ:
            raise ValueError('Unbound identifier: ' + a)
        return self.Γ[a].under(self)

    def fix(self, a):
        self.fixed |= a
        self.hash = self.simple = None
        return self

    def gen(self, t, blacklist=set()):
        names = self.fixed - blacklist
        t = t.under(self).gen(names)
        self.σ.gen(names)
        for k, v in self.Γ.items():
            self.Γ[k] = self.Γ[k].gen(names)
        self.F = self.F.gen(names)
        self.hash = self.simple = None
        return t

    def instantiate(self, t):
        t = t.under(self)
        return t.fresh(self.fixed).flipped(self.fixed)

    def find(self, a):
        return self.σ.find(a)

    def union(self, a, b):
        self.σ.union(a, b)
        self.names |= U.names_of(a) | U.names_of(b)
        self.hash = self.simple = None
        return self

    def assume(self, G):
        self.F = T.And(self.F, G.under(self))
        self.names |= U.names_of(G)
        self.hash = self.simple = None
        return self

    def evars(self):
        return self.σ.evars() | self.F.evars()

    def uvars(self):
        return self.σ.uvars() | self.F.uvars()

    def free_vars(self):
        return self.F.vars() | self.σ.free_vars()

    def to_z3(self):
        import z3
        return z3.Implies(self.F.to_z3(), self.σ.to_z3())

    def unify(self, a, b):
        T.unify(a, b, self.σ)
        return self

# multiple possible Contexts + ability to branch on new conditions
class State:
    def __init__(self, contexts = None):
        self.contexts = [Context()] if contexts is None else contexts

    def __str__(self):
        return '\n'.join(str(a) for a in self.contexts)

    def __iter__(self):
        return iter(self.contexts)

    def __contains__(self, a):
        return all(a in c for c in self.contexts)

    def evars(self):
        return U.mapreduce(U.union, U.evars, self.contexts, set())

    def uvars(self):
        return U.mapreduce(U.union, U.uvars, self.contexts, set())

    def free_vars(self):
        return U.mapreduce(U.union, U.free_vars, self.contexts, set())

    def to_z3(self):
        import z3
        return z3.And([c.to_z3() for c in self.contexts])

# --------------------------------------------------------------------------------

if __name__ == '__main__':
    # TODO if statements
    print(Context().to_z3())
    print(Context().evars())
    print(Context().uvars())

    c = Context()
    c.push()
    print(c)
    c.annotate('a', T.AVar(T.UVar('a')) + 1)
    c.union(1, 2)
    c.assume(T.BVar(T.UVar('a')))
    print(c)
    c.undo()
    print(c)

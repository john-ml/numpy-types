import util as U
import pattern as P
import nptype as T
import substitution as S

# substitution map + typing environment under some precondition
class Context:
    def __init__(self):
        self.σ = S.Substitution(lambda a, b: a << b)
        self.Γ = {}
        self.F = T.BLit(True)

    def __str__(self):
        return '{} -> {} ({})'.format(self.F, U.typedict(self.Γ), self.σ)

    def copy(self):
        c = Context()
        c.σ = self.σ.copy()
        c.Γ = dict(self.Γ)
        c.F = self.F
        return c

    def annotate(self, a, t):
        self.Γ[a] = t

    def typeof(self, a):
        return self.Γ[a]

    def find(self, a):
        return self.σ.find(a)

    def union(self, a, b):
        self.σ.union(a, b)
        return self

    def assume(self, G):
        self.F = T.And(F, G)

    def evars(self):
        return self.σ.evars()

    def tvars(self):
        return self.σ.tvars()

    def to_z3(self):
        import z3
        return z3.Implies(self.F.to_z3(), self.σ.to_z3())

# multiple possible Contexts
class State:
    def __init__(self):
        self.contexts = [Context()]

    def __str__(self):
        return '\n'.join(str(a) for a in self.contexts)

    def __iter__(self):
        return iter(self.contexts)

    def fork(self, F):
        contexts = [c.copy() for c in self.contexts]
        for c in self.contexts:
            c.assume(F)
        for c in contexts:
            c.assume(T.Not(f))
        self.contexts.extend(contexts)
        return self

    def copy(self):
        s = State()
        s.contexts = [a.copy() for a in self.contexts]
        return s

    def annotate(self, a, t):
        for c in self.contexts:
            c.annotate(a, t)

    def typeof(self, a):
        return [c.typeof(a) for c in self.contexts]

    def find(self, a):
        return [c.find(a) for c in self.contexts]

    def union(self, a, b):
        for c in self.contexts:
            c.union(a, b)
        return self

    def assume(self, G):
        for c in self.contexts:
            c.assume(G)

    def evars(self):
        return U.reducemap(U.union, U.evars, self.contexts, set())

    def tvars(self):
        return U.reducemap(U.union, U.tvars, self.contexts, set())

    def to_z3(self):
        import z3
        return z3.Implies(self.F.to_z3(), self.σ.to_z3())

# unification, lifted to State
def unify(a, b, s):
    for c in s:
        T.unify(a, b, c)
    return s

# --------------------------------------------------------------------------------

if __name__ == '__main__':
    # TODO if statements

    print('\n'.join(map(str, rules)))
    print(Context().to_z3())
    print(Context().evars())
    print(Context().tvars())

    a = State()
    print([b.union(1, 2) for b in a])
    print(a)

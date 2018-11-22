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
        self.history = []

    def __str__(self):
        return '{} -> {} ({})'.format(self.F, U.typedict(self.Γ), self.σ)

    def copy(self):
        c = Context()
        c.σ = self.σ.copy()
        c.Γ = dict(self.Γ)
        c.F = self.F
        return c

    # TODO: test push, pop, undo (esp make sure its ok to just store self.F and not self.F.copy())
    def push(self):
        self.σ.push()
        self.history.append((dict(self.Γ), self.F))
        return self

    def pop(self):
        self.σ.pop()
        self.history.pop()
        return self

    def undo(self):
        self.σ.undo()
        self.Γ, self.F = self.history.pop()
        return self

    def annotate(self, a, t):
        self.Γ[a] = t
        return self

    def typeof(self, a):
        return self.Γ[a]

    def find(self, a):
        return self.σ.find(a)

    def union(self, a, b):
        self.σ.union(a, b)
        return self

    def assume(self, G):
        self.F = T.And(self.F, G)
        return self

    def evars(self):
        return self.σ.evars()

    def tvars(self):
        return self.σ.tvars()

    def to_z3(self):
        import z3
        return z3.Implies(self.F.to_z3(), self.σ.to_z3())

# multiple possible Contexts + ability to branch on new conditions
class State:
    def __init__(self):
        self.contexts = [Context()]

    def __str__(self):
        return '\n'.join(str(a) for a in self.contexts)

    def __iter__(self):
        return iter(self.contexts)

    # return two copies of state s, s' where s assumes F and s' assumes ¬F
    def fork(self, F):
        s = State()
        s.contexts = [c.copy().assume(T.Not(F)) for c in self.contexts]

        for c in self.contexts:
            c.assume(F)
        return self, s

    # steal contexts from other
    def join(self, other):
        self.contexts.extend(other.contexts)
        return self

    def copy(self):
        s = State()
        s.contexts = [a.copy() for a in self.contexts]
        return s

    def push(self):
        for c in self.contexts:
            c.push()

    def pop(self):
        for c in self.contexts:
            c.pop()

    def undo(self):
        for c in self.contexts:
            c.undo()

    def annotate(self, a, t):
        for c in self.contexts:
            c.annotate(a, t)
        return self

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
        return self

    def evars(self):
        return U.mapreduce(U.union, U.evars, self.contexts, set())

    def tvars(self):
        return U.mapreduce(U.union, U.tvars, self.contexts, set())

    def to_z3(self):
        import z3
        return z3.And([c.to_z3() for c in self.contexts])

    def run(self, *actions):
        for f in actions:
            f(self)
        return self

# unification, lifted to State
def unify(a, b, s):
    s.push()
    try:
        for c in s:
            T.unify(a, b, c)
        s.pop()
        return s
    except ValueError as e:
        s.undo()
        raise

# --------------------------------------------------------------------------------

if __name__ == '__main__':
    # TODO if statements
    print(Context().to_z3())
    print(Context().evars())
    print(Context().tvars())

    a = State()
    print([b.union(1, 2) for b in a])
    print(a)

    s = State()
    print(s)
    print()
    s, s1 = s.fork(T.BVar(T.TVar('a')))
    unify(T.BVar(T.EVar('a')), T.BLit(True), s1)
    print(s)
    print()
    print(s1)
    print()

    s.join(s1)
    print(s)
    print()
    try:
        unify(T.BVar(T.EVar('a')), T.BLit(False), s)
    except ValueError as e:
        print(e)
    print(s)
    print()

    print(s.tvars())
    print(s.evars())
    print(U.to_quantified_z3(s))

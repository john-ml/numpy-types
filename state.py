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
        self.history = []

    def __str__(self):
        return '{} -> {} ({})'.format(self.F, U.typedict(self.Γ), self.σ)

    def __contains__(self, a):
        return a in self.Γ

    def copy(self):
        c = Context()
        c.σ = self.σ.copy()
        c.Γ = dict(self.Γ)
        c.F = self.F
        return c

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
        if a not in self.Γ:
            raise ValueError('Unbound identifier: ' + a)
        return self.Γ[a].under(self)

    def find(self, a):
        return self.σ.find(a)

    def union(self, a, b):
        self.σ.union(a, b)
        return self

    def assume(self, G):
        self.F = T.And(self.F, G)
        return self

    def evars(self):
        return self.σ.evars() | self.F.evars()

    def tvars(self):
        return self.σ.tvars() | self.F.tvars()

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

    def tvars(self):
        return U.mapreduce(U.union, U.tvars, self.contexts, set())

    def to_z3(self):
        import z3
        return z3.And([c.to_z3() for c in self.contexts])

# --------------------------------------------------------------------------------

if __name__ == '__main__':
    # TODO if statements
    print(Context().to_z3())
    print(Context().evars())
    print(Context().tvars())

    c = Context()
    c.push()
    print(c)
    c.annotate('a', T.AVar(T.TVar('a')) + 1)
    c.union(1, 2)
    c.assume(T.BVar(T.TVar('a')))
    print(c)
    c.undo()
    print(c)

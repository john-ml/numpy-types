import pattern as P
from nptype import *
import substitution as S
import util as U

class Rule:
    def __init__(self, pattern, captures, returns=None, forces={}):
        self.s = pattern
        self.pattern = P.make_pattern(pattern)
        self.captures = captures
        self.returns = returns
        self.forces = forces

    def __str__(self):
        return '{} |- {}{}{}'.format(
            U.typedict(self.captures),
            self.s,
            ('' if self.returns is None else ' : {}'.format(self.returns)),
            ('' if self.forces == {} else ' => {}'.format(U.typedict(self.forces))))

class Context:
    def __init__(self):
        self.σ = S.Substitution(compare)
        self.Γ = {}
        self.F = BLit(True)

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
        self.F = And(F, G)

    def evars(self):
        return self.σ.evars()

    def tvars(self):
        return self.σ.tvars()

    def to_z3(self):
        import z3
        return z3.Implies(self.F.to_z3(), self.σ.to_z3())

class State:
    def __init__(self):
        self.contexts = [Context()]

    def __str__(self):
        return '\n'.join(str(a) for a in self.contexts)

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
        #TODO exceptions
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

if __name__ == '__main__':
    rules = [
        Rule(
            # a : array[n, m] |- a.shape[0] : (n : int)
            '_a.shape[0]',
            {'a': Array([AVar(TVar('n')), AVar(TVar('m'))])},
            returns = AVar(TVar('n'))),
        Rule(
            # a : (n : int), b : (m : int) |- a + b : (n + m : int)
            '_a + _b',
            {'a': AVar(TVar('n')), 'b': AVar(TVar('m'))},
            returns = AVar(TVar('n')) + AVar(TVar('m'))),
        Rule(
            # a : (n : int), b : (m : int) |- a = b => a : (m : int)
            '_a = _b',
            {'a': AVar(TVar('n')), 'b': AVar(TVar('m'))},
            forces = {'a': AVar(TVar('m'))})]

    # TODO if statements

    print('\n'.join(map(str, rules)))
    print(Context().to_z3())
    print(Context().evars())
    print(Context().tvars())

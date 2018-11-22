import util as U
import pattern as P

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

if __name__ == '__main__':
    rules = [
        Rule(
            # a : array[n, m] |- a.shape[0] : (n : int)
            '_a.shape[0]',
            {'a': T.Array([T.AVar(T.TVar('n')), T.AVar(T.TVar('m'))])},
            returns = T.AVar(T.TVar('n'))),
        Rule(
            # a : (n : int), b : (m : int) |- a + b : (n + m : int)
            '_a + _b',
            {'a': T.AVar(T.TVar('n')), 'b': T.AVar(T.TVar('m'))},
            returns = T.AVar(T.TVar('n')) + T.AVar(T.TVar('m'))),
        Rule(
            # a : (n : int), b : (m : int) |- a = b => a : (m : int)
            '_a = _b',
            {'a': T.AVar(T.TVar('n')), 'b': T.AVar(T.TVar('m'))},
            forces = {'a': T.AVar(T.TVar('m'))})]

    print('\n'.join(map(str, rules)))

import util as U
import nptype as T
import pattern as P
import state as S

# pattern + action
# names of arguments to action should match names of capture groups in pattern
class Rule:
    def __init__(self, pattern, action):
        self.s = pattern
        self.pattern = P.make_pattern(pattern)
        self.f = action

    # def run(self, ast):

# action combinators?

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

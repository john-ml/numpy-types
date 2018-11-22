from pattern import *
from nptype import *

class Rule:
    def __init__(self, pattern, captures, returns=None, forces={}):
        self.s = pattern
        self.pattern = make_pattern(pattern)
        self.captures = captures
        self.returns = returns
        self.forces = forces

    def __str__(self):
        typedict = lambda d: \
            ', '.join('{} : {}'.format(k, v) for k, v in d.items())
        return '{} |- {}{}{}'.format(
            typedict(self.captures),
            self.s,
            ('' if self.returns is None else ' : {}'.format(self.returns)),
            ('' if self.forces == {} else ' => {}'.format(typedict(self.forces))))

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

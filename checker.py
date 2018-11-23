import util as U
import pattern as P
import state as S
import ast as A
import nptype as T

# pattern + action
# action is function(self : Checker, **kwargs)
# names of arguments should match names of capture groups in pattern
class Rule:
    def __init__(self, pattern, action, name=None):
        self.pattern = pattern
        self.f = action
        self.name = name

# type-checker acting on a set of checking rules
class Checker:
    def __init__(self, rules):
        self.state = S.State()
        self.rules = rules

    def push(self):
        self.state.push()

    def pop(self):
        self.state.pop()

    def undo(self):
        self.state.undo()

    # try each of the rules in order
    # return result of action corresponding to first matching rule
    # succeed (having checked nothing) if no rules match
    # fail if all rules that matched threw
    def analyze(self, ast):
        errors = []
        for rule in self.rules:
            try:
                matches = P.matches(rule.pattern, ast)
                if matches is None:
                    continue
                self.push()
                result = rule.f(self, **matches)
                print('analyze({})\n==> {}{}\n'.format(
                    P.pretty(P.explode(ast)),
                    result,
                    ('\n(by {})'.format(rule.name) if rule.name is not None else '')))
                self.pop()
                return result
            except ValueError as e:
                self.undo()
                errors.append(e)
        if len(errors) > 0:
            raise ValueError(
                'Typechecking failed. TODO pretty-print this: ' +
                str(errors))

    def check(self, ast):
        import z3

        self.push()
        self.analyze(ast)
        F = U.to_quantified_z3(self.state)
        self.undo()

        print('F =', F)
        s = z3.Solver()
        s.add(F)
        if s.check() != z3.sat:
            raise ValueError(
                'Typechecking failed. Unsatisfiable constraint: ' +
                str(F))

# -------------------- basic type-checking rules --------------------

def make_rule(s, f, name=None):
    return Rule(P.make_pattern(s), f, name)

def analyze_module(self, body):
    for a in body:
        self.analyze(a)
module = Rule(P.raw_pattern('__body'), analyze_module, 'module')

lit_True = make_rule('True', lambda self: T.BLit(True), 'lit_True')
lit_False = make_rule('False', lambda self: T.BLit(False), 'lit_False')
test = make_rule('_a = _b', lambda self, a, b: (a, self.analyze(b)), 'test')

# TODO: special cases e.g. 1, 2, 3, ... => type is int

if __name__ == '__main__':
    c = Checker([module, lit_True, lit_False, test])
    c.check(A.parse('a = True\nb = False'))

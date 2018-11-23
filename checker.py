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

# type-checker doesn't know what to do
class ConfusionError(Exception):
    pass

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
    # fail with ConfusionError if no rules match
    # fail with ValueError if all rules that matched threw
    def analyze(self, ast):
        errors = []
        for rule in self.rules:
            try:
                matches = P.matches(rule.pattern, ast)
                if matches is None:
                    continue
                self.push()
                result = rule.f(self, **matches)
                print('analyze({})\n={}=> {}\nstate = {}\n'.format(
                    P.pretty(P.explode(ast)),
                    ('({})'.format(rule.name) if rule.name is not None else ''),
                    result,
                    self.state))
                self.pop()
                return result
            except ValueError as e:
                self.undo()
                errors.append(e)
        if len(errors) > 0:
            raise ValueError(
                'Typechecking failed. TODO pretty-print this: ' +
                str(errors))
        raise ConfusionError(
            'TODO pretty-print this: ' +
            str(self.rules) +
            P.pretty(P.explode(ast)))

    def check(self, ast):
        import z3

        self.analyze(ast)
        F = U.to_quantified_z3(self.state)

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

def unary_recursion(f):
    return lambda self, a: f(self.analyze(a))

def binary_recursion(f):
    return lambda self, a, b: f(self.analyze(a), self.analyze(b))

def expression(s, assumptions, return_type, name=None):
    def f(self, **kwargs):
        names = ({v.name for _, t in assumptions.items() for v in t.vars()} |
                 {v.name for v in return_type.vars()})
        renaming = dict(zip(names, T.fresh_ids))
        for a, ast in kwargs.items():
            self.state.unify(self.analyze(ast), assumptions[a].renamed(renaming).flipped())
        return return_type.renamed(renaming).flipped()
    return Rule(P.make_pattern(s), f, name)

def analyze_module(self, body):
    for a in body:
        self.analyze(a)
module = Rule(P.raw_pattern('__body'), analyze_module, 'module')

def assignment(self, a, b):
    t = self.analyze(b)
    # TODO check if basic types are compatible?
    # TODO handle things other than just name nodes?
    assert type(a) is A.Name
    self.state.annotate(a.id, t)
assign = make_rule('_a = _b', assignment, 'assign')

# TODO: special cases e.g. 1, 2, 3, ... => type is int

if __name__ == '__main__':
    lit_True = make_rule('True', lambda self: T.BLit(True), 'lit_True')
    lit_False = make_rule('False', lambda self: T.BLit(False), 'lit_False')
    bool_not = expression(
        'not _a', {'a': T.BVar(T.TVar('a'))}, T.Not(T.BVar(T.TVar('a'))), 'bool_not')
    bool_or = expression(
        '_a or _b',
        {'a': T.BVar(T.TVar('a')), 'b': T.BVar(T.TVar('b'))},
        T.Or(T.BVar(T.TVar('a')), T.BVar(T.TVar('b'))),
        'bool_or')
    c = Checker([module, assign, lit_True, lit_False, bool_or, bool_not])
    c.check(A.parse('a = True or not False'))

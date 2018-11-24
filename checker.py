import util as U
import pattern as P
import state as S
import ast as A
import nptype as T

# typechecking rule
# action : Checker * Context * ..kwargs -> [Context * ?a]
# names of arguments should match names of capture groups in pattern
class Rule:
    def __init__(self, pattern, action, name=None):
        self.pattern = pattern
        self.action = action
        self.name = name

# checker doesn't know what to do
class ConfusionError(Exception):
    pass

# type-checker acting on a set of checking rules
class Checker:
    def __init__(self, rules):
        self.rules = rules

    # try each of the rules in order and run action corresponding to first matching rule
    # Checker * [Context] * AST * (Context * a -> [Context * b]) -> [Context * b]
    # fail with ConfusionError if no rules match
    # fail with ValueError if all rules that matched threw
    def analyze(self, contexts, ast, f = lambda s, a: [(s, a)]):
        #if type(ast) is A.Name:
        #    if ast.id in self.state:
        #        # to read from the variable ast.id, all possible types must be equivalent
        #        fresh = T.EVar(next(T.fresh_ids))
        #        for c in self.state:
        #            c.unify(fresh, c.typeof(ast.id))
        #        return fresh
        #    else:
        #        raise ValueError('Unbound identifier: ' + ast.id)
        pairs = []
        for context in contexts:
            errors = []
            for rule in self.rules:
                try:
                    matches = P.matches(rule.pattern, ast)
                    if matches is None:
                        continue
                    new_pairs = rule.action(self, context.copy(), **matches)
                    new_pairs = [b for s, a in new_pairs for b in f(s, a)]
                    pairs.extend(new_pairs)
                    break
                except ValueError as e:
                    errors.append(e)
            else:
                if errors == []:
                    raise ConfusionError(
                        'TODO pretty-print this: ' +
                        str(self.rules) +
                        P.pretty(P.explode(ast)))
                raise ValueError(
                    'TODO pretty-print this: ' +
                    str(errors))
        return pairs

    def check(self, ast):
        import z3

        pairs = self.analyze([S.Context()], ast)
        state = S.State([s for s, _ in pairs])
        F = U.to_quantified_z3(state)

        print('state =', state)
        print('F =', F)
        s = z3.Solver()
        s.add(F)
        if s.check() != z3.sat:
            raise ValueError(
                'Unsatisfiable constraint: ' +
                str(F))

# -------------------- basic type-checking rules --------------------

def module_action(self, context, body):
    if body == []:
        return [(context, None)]
    h, t = body[0], body[1:]
    result = self.analyze([context], h, lambda new_context, _:
        module_action(self, new_context, t))
    return result
module = Rule(P.raw_pattern('__body'), module_action, 'module')

def assignment(self, context, lhs, rhs):
    assert type(lhs) is A.Name
    def k(new_context, new_t):
        if lhs.id in new_context:
            old_t = new_context.typeof(lhs.id)
            if not (isinstance(old_t, T.AExp) and isinstance(new_t, T.AExp) or
                    isinstance(old_t, T.BExp) and isinstance(new_t, T.BExp)):
                new_context.unify(old_t, new_t)
        new_context.annotate(lhs.id, new_t)
        return [(new_context, None)]
    result = self.analyze([context], rhs, k)
    return result
assign = Rule(P.make_pattern('_lhs = _rhs'), assignment, 'assign')

# given a pattern string s, and assumptions about the types of each capture group,
# return return_type
def expression(s, assumptions, return_type, name=None):
    def f(self, context, **kwargs):
        names = ({v.name for _, t in assumptions.items() for v in t.vars()} |
                 {v.name for v in return_type.vars()})
        def loop(context, pairs, analyzed):
            if pairs == []:
                renaming = dict(zip(names, T.fresh_ids))
                instantiate = lambda t: t.renamed(renaming).flipped()
                for name, inferred_type in analyzed:
                    context.unify(inferred_type, instantiate(assumptions[name]))
                return [(context, instantiate(return_type))]
            (name, ast), tail = pairs[0], pairs[1:]
            return self.analyze([context], ast, lambda new_context, inferred_type:
                loop(new_context, tail, analyzed + [(name, inferred_type)]))
        return loop(context, list(kwargs.items()), [])
    return Rule(P.make_pattern(s), f, name)

def literal(s, t, name=None):
    return Rule(P.make_pattern(s), lambda _, context: [(context, t)], name)

# binary infix operator op and corresponding variable type v and type constructor f
def binary_operator(op, v, f, name=None):
    return expression(
        '_a {} _b'.format(op), 
        {'a': v(T.TVar('a')), 'b': v(T.TVar('b'))},
        f(v(T.TVar('a')), v(T.TVar('b'))),
        name)

## TODO: special cases e.g. 1, 2, 3, ... => type is int

if __name__ == '__main__':
    lit_None = literal('None', T.TNone())
    lit_True = literal('True', T.BLit(True))
    lit_False = literal('False', T.BLit(False))
    bool_or = binary_operator('or', T.BVar, T.Or, 'bool_or')
    bool_and = binary_operator('and', T.BVar, T.And, 'bool_and')
    bool_not = expression(
        'not _a',
        {'a': T.BVar(T.TVar('a'))},
        T.Not(T.BVar(T.TVar('a'))),
        'bool_not')
    lit_0 = literal('0', T.ALit(0))
    lit_1 = literal('1', T.ALit(1))
    int_add = binary_operator('+', T.AVar, T.Add, 'int_add')
    int_mul = binary_operator('*', T.AVar, T.Mul, 'int_mul')

    c = Checker([
        module, assign,
        lit_None, lit_True, lit_False,
        lit_0, lit_1, int_add, int_mul,
        bool_or, bool_and, bool_not])
    c.check(A.parse('''
a = True or False
a = not False
b = (1 + 1) * (1 + 1 + 1)
''')) #\na = a and False')) #\na = None'))

import util as U
import pattern as P
import context as C
import ast as A
import nptype as T

# typechecking rule
# action : Checker * Context * ..kwargs -> [Context * ?a]
# names of arguments should match names of capture groups in pattern
class Rule:
    def __init__(self, pattern, action, name=None):
        self.s = pattern if type(pattern) is str else None
        self.pattern = P.make_pattern(pattern) if type(pattern) is str else pattern
        self.action = action
        self.name = name

    def __str__(self):
        if self.s is not None:
            return '{} ({})'.format(self.s, self.name)
        else:
            return '{} ({})'.format(P.pretty(P.explode(self.pattern)), self.name)

class ASTError(Exception):
    def __init__(self, ast):
        self.ast = ast # problematic subtree

# type-checking failed
class CheckError(ASTError):
    def __init__(self, ast, errors):
        self.ast = ast
        self.errors = errors # rules attempted and errors they produced

    def __str__(self):
        return '{}\nfor:\n{}'.format(
            P.pretty(P.explode(self.ast)),
            '\n'.join('{}\n{}'.format(
                r.name,
                U.indent('  ', str(e))) for r, e in self.errors))

    # pretty-print the error, where s is the source code that was being analyzed
    def pretty(self, s):
        pretty = lambda e: (e.pretty(s) if type(e) in (CheckError, ConfusionError) else str(e))
        snippet = ''
        if any(type(e) is not CheckError for _, e in self.errors):
            snippet = U.highlight(self.ast, s) + '\n'
        return snippet + '\n\n'.join(pretty(e) for _, e in self.errors)

# no suitable pattern
class ConfusionError(ASTError):
    def __init__(self, ast):
        self.ast = ast
    def pretty(self, s):
        return 'No applicable rule:\n{}'.format(U.highlight(self.ast, s))

# type-checker acting on a set of checking rules
class Checker:
    def __init__(self, rules, return_type=T.TNone(), careful=False):
        self.rules = rules
        self.return_type = return_type
        self.careful = careful

    # try each of the rules in order and run action corresponding to first matching rule
    # Checker
    # * [Context]
    # * AST
    # * (Context * a -> [Context * b])
    # -> [Context * b]
    # fail with ConfusionError if no rules match
    # fail with CheckError if all rules that matched threw
    def analyze(self, contexts, ast, f = lambda s, a: [(s, a)]):
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
                except (ValueError, CheckError, ConfusionError) as e:
                    errors.append((rule, e))
            else:
                if errors == []:
                    raise ConfusionError(ast)
                raise CheckError(ast, errors)
        return pairs

    def check(self, ast):
        try:
            pairs = self.analyze([C.Context()], ast)
            state = C.State([s for s, _ in pairs])
            return U.verify(state)
        except (ValueError, CheckError) as e:
            if not self.careful:
                Checker(self.rules, self.return_type, careful=True).check(ast)
            else:
                raise

# -------------------- rule/checker combinators --------------------

# given a pattern string s, and assumptions about the types of each capture group,
# return return_type
def expression(s, assumptions, return_type, name=None):
    to_type = lambda a: (T.parse(a) if type(a) is str else a)
    assumptions = dict((k, to_type(v)) for k, v in assumptions.items())
    return_type = to_type(return_type)
    def f(self, context, **kwargs):
        names =  {v for _, t in assumptions.items() for v in t.names()} | return_type.names()
        def loop(context, pairs, analyzed):
            if pairs == []:
                # TODO better way of naming
                renaming = dict(zip(names, map(lambda a: 'tmp' + a, T.fresh_ids)))
                instantiate = lambda t: t.renamed(renaming).flipped()
                for name, inferred_type in analyzed:
                    context.unify(inferred_type, instantiate(assumptions[name]))
                if self.careful:
                    U.verify(context)
                return [(context, instantiate(return_type))]
            (name, ast), tail = pairs[0], pairs[1:]
            return self.analyze([context], ast, lambda new_context, inferred_type:
                loop(new_context, tail, analyzed + [(name, inferred_type)]))
        return loop(context, list(kwargs.items()), [])
    return Rule(s, f, name)

def literal(s, t, name=None):
    return Rule(s, lambda _, context: [(context, t)], name)

# binary infix operator op and corresponding variable type v and type constructor f
def binary_operator(op, v, f, name=None):
    return expression(
        '_a {} _b'.format(op), 
        {'a': v(T.parse('a')), 'b': v(T.parse('b'))},
        f(v(T.parse('a')), v(T.parse('b'))),
        name)

no_op = lambda s, a: [(s, a)]

# extend an environment
def extend(self, context, bindings, k=no_op):
    c = context.copy()
    for a, t in bindings.items():
        t = T.parse(t)
        c.annotate(a, t)
    return k(c, None)

# -------------------- basic type-checking rules --------------------

def analyze_body(self, context, body, k=no_op):
    if body == []:
        return k(context, None)
    h, t = body[0], body[1:]
    return self.analyze([context], h, lambda new_context, _:
        analyze_body(self, new_context, t, k))

module = Rule(P.raw_pattern('__body'), analyze_body, 'module')

def analyze_cond(self, context, t, top, bot, k=no_op):
    top_context = context.copy().assume(t)
    bot_context = context.copy().assume(T.Not(t))
    top_results = analyze_body(self, top_context, top)
    bot_results = analyze_body(self, bot_context, bot)
    return [b
        for s, a in top_results + bot_results
        for b in k(s, a)]

cond = Rule('''
if _p:
    __top
else:
    __bot
''',
lambda self, context, p, top, bot:
    self.analyze([context], p, lambda new_context, t:
        analyze_cond(self, new_context, t, top, bot)),
'cond')

skip = Rule('pass', lambda self, context: [(context, None)], 'skip')

def analyze_cond_expr(self, context, t, l, r, k=no_op):
    top_context = context.copy().assume(t)
    bot_context = context.copy().assume(T.Not(t))
    top_results = self.analyze([top_context], l)
    bot_results = self.analyze([bot_context], r)
    return [b
        for s, a in top_results + bot_results
        for b in k(s, a)]

cond_expr = Rule(
    '_l if _p else _r',
    lambda self, context, l, p, r:
        self.analyze([context], p, lambda new_context, t:
            analyze_cond_expr(self, new_context, t, l, r)),
    'cond_expr')

def analyze_assign(self, context, lhs, rhs):
    assert type(lhs) is A.Name
    def k(new_context, new_t):
        if U.ident2str(lhs) in new_context:
            old_t = new_context.typeof(U.ident2str(lhs))
            if not (isinstance(old_t, T.AExp) and isinstance(new_t, T.AExp) or
                    isinstance(old_t, T.BExp) and isinstance(new_t, T.BExp)):
                new_context.unify(old_t, new_t)
        new_context.annotate(U.ident2str(lhs), new_t)
        return [(new_context, None)]
    return self.analyze([context], rhs, k)

assign = Rule('_lhs = _rhs', analyze_assign, 'assign')

def analyze_ident(self, context, a):
    return [(context, context.typeof(U.ident2str(a)))]

ident = Rule('a__Name', analyze_ident, 'ident')
attr_ident = Rule('a__Attribute', analyze_ident, 'attr_ident')

def analyze_fun_def(self, context, f, args, return_type, body):
    arg_types = []
    nested_context = context.copy()
    for arg in args:
        a, t = T.from_ast(arg)
        nested_context.annotate(a, t)
        arg_types.append(t)
    r = T.from_ast(return_type)
    fun_type = T.Fun(T.Tuple(arg_types), r)
    nested_context.annotate(f, fun_type)
    return analyze_body(
        Checker(self.rules, return_type=r, careful=self.careful),
        nested_context, body,
        lambda new_context, _: (lambda _:
            [(context.annotate(f, fun_type), None)])(U.verify(new_context)))

fun_def = Rule('''
def _f(__args) -> _return_type:
    __body''', analyze_fun_def, 'fun_def')

lit_None = literal('None', T.TNone())
lit_True = literal('True', T.BLit(True))
lit_False = literal('False', T.BLit(False))

bool_or = binary_operator('or', T.BVar, T.Or, 'bool_or')
bool_and = binary_operator('and', T.BVar, T.And, 'bool_and')
bool_not = expression('not _a', {'a': 'bool(a)'}, 'not bool(a)', 'bool_not')

lit_num = Rule('num__Num', lambda _, context, num:
    [(context, T.ALit(int(num.n)))], 'lit_num')
int_add = binary_operator('+', T.AVar, T.Add, 'int_add')
int_mul = binary_operator('*', T.AVar, T.Mul, 'int_mul')

ret = Rule('return _a', lambda self, context, a:
    self.analyze([context], a, lambda new_context, t:
        [(new_context.unify(self.return_type, t), None)]), 'return')

def analyze_fun_call(self, context, f, args):
    def loop(context, l, arg_types):
        if l == []:
            arg_type = T.Tuple(arg_types)
            fn_type = context.typeof(U.ident2str(f)).fresh().flipped()
            context.unify(arg_type, fn_type.a)
            return [(context, fn_type.b)]
        h, t = l[0], l[1:]
        return self.analyze([context], h, lambda new_context, inferred_type:
            loop(new_context, t, arg_types + [inferred_type]))
    return loop(context, args, [])

fun_call = Rule('_f(__args)', analyze_fun_call, 'fun_call')

print_expr = expression('print(_a)', {'a': T.TVar('a')}, T.TNone(), 'print_expr')
print_stmt = Rule(
    P.raw_pattern('print(_a)').body[0],
    lambda self, context, a:
        self.analyze([context], a, lambda new_context, inferred_type:
            [(new_context, None)]))

# -------------------- basic rule set --------------------

basic_rules = [
    module,
    assign,
    skip,
    ident,
    attr_ident,
    lit_None, lit_True, lit_False, lit_num,
    bool_or, bool_and, bool_not, int_add, int_mul,
    cond, cond_expr,
    fun_def,
    fun_call,
    ret,
    print_expr,
    print_stmt]

if __name__ == '__main__':
    arr_zeros = expression('np.zeros(_a)', {'a': 'int(a)'}, 'array[int(a)]', 'arr_zeros')
    add_row = expression('add_row(_a)', {'a': 'array[int(a)]'}, 'array[int(a) + 1]', 'add_row')
    smush = expression(
        'smush(_a, _b)',
        {'a': 'array[int(a)]', 'b': 'array[int(a)]'},
        'array[int(a)]', 'smush')
    import_numpy = Rule('import numpy as np',
        lambda self, context: extend(self, context, {
            'np.ones': 'Fun((int(a),), array[a])'}),
        'import_numpy')

    def try_check(s, careful=False):
        rules = basic_rules + [arr_zeros, add_row, smush, import_numpy]
        c = Checker(rules, return_type=T.parse('array[3]'), careful=careful)
        try:
            c.check(A.parse(s))
            print('OK')
        except (ValueError, ConfusionError, CheckError) as e:
            if type(e) in (CheckError, ConfusionError):
                print(e.pretty(s))
            else:
                print(e)
        finally:
            print()

    try_check('''
a = True
a = None
''')

    try_check('''
d = add_row(np.zeros(3))
e = add_row(d)
f = smush(d, e)
''')

    try_check('''
a = True or False
a = not False
b = (1 + 1) * (1 + 1 + 1)
c = np.zeros(3)
''')

    try_check('''
a = add_row(np.zeros(2))
return a
b = np.zeros(3)
return b
c = np.zeros(1 + 1 + 1)
return c
''')

    try_check('''
n = 1
m = 1
if False:
    n = n + 1
else:
    m = m + 1
a = np.zeros(n + m)
b = smush(a, np.zeros(3))
''')

    try_check('''
def f(p: bool, a: int, b: array[a]) -> array[a + 1]:
    if p:
        return np.zeros(1 + a)
    else:
        return smush(add_row(b), np.zeros(a + 2))
''')

    try_check('''
def f(p : bool, n : int) -> array[n + 2]:
    if p:
        n = 1 + n
        r = np.zeros(n)
    else:
        r = np.zeros(n + 1)
    return smush(add_row(r), np.zeros(n + 1 if p else n + 2))
''')

    try_check('''
def succ(a : int) -> int:
    return a + 1
n = 3
a = np.zeros(succ(n))
''')

    try_check('''
a += 1
''')

    try_check('''
import numpy as np
a = np.ones(3)
b = np.zeros(4)
c = smush(a, b)
''')

    try_check('''
import numpy as np
a = np.ones(3)
b = np.zeros(3)
c = smush(a, b)
''')

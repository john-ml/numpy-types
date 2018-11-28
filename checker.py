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
        def error_paths(self):
            if type(self) is not CheckError:
                return [[self]]
            paths = []
            for _, e in self.errors:
                paths.extend([[self] + p for p in error_paths(e)])
            return paths

        paths = error_paths(self)

        def pretty(e):
            if type(e[-1]) is ConfusionError:
                return e[-1].pretty(s)
            return '{}\n{}'.format(U.highlight(e[-2].ast, s), str(e[-1]))

        if len(paths) == 1:
            return pretty(paths[0])

        value_errors = [p for p in paths
            if type(p[-1]) is ValueError and 'Unbound identifier' not in str(p[-1])]
        unbound_idents = [p for p in paths
            if type(p[-1]) is ValueError and 'Unbound identifier' in str(p[-1])]
        unif_errors = [p for p in paths if type(p[-1]) is T.UnificationError]
        grouped_unif_errors = {}
        for reason in {p[-1].reason for p in unif_errors}:
            grouped_unif_errors[reason] = [p for p in unif_errors if p[-1].reason == reason]
        confusion_errors = [p for p in paths if type(p[-1]) is ConfusionError]

        summary = ''
        if len(value_errors) > 0:
            summary = '{} value errors'.format(len(value_errors))
        if len(unbound_idents) > 0:
            summary += '\n{} unbound identifier errors'.format(len(unbound_idents))
        if len(grouped_unif_errors.items()) > 0:
            for reason, paths in grouped_unif_errors.items():
                summary += '\n{} unification errors ({})'.format(len(paths), reason)
        if len(confusion_errors) > 0:
            summary += '\n{} confusion errors'.format(len(confusion_errors))

        if len(value_errors) > 0:
            header = '' if summary == '' else 'Among\n' + U.indent('  ', summary)
            return header + ''.join('\n' + pretty(e) for e in value_errors)

        if len(confusion_errors) > 0:
            header = '' if summary == '' else 'Among\n' + U.indent('  ', summary)
            return header + ''.join('\n' + pretty(e) for e in confusion_errors)

        coords = {U.coords(p[-2].ast) for p in paths}
        footer = summary if len(paths) > 10 else '\n'.join({str(p[-1]) for p in paths})
        return '{}\n{}'.format(
            '\n'.join(
                U.code_pointers(row, [c for r, c in coords if r == row], s)
                for row in {r for r, _ in coords}),
            footer)

# no suitable pattern
class ConfusionError(ASTError):
    def __init__(self, ast):
        self.ast = ast
    def pretty(self, s):
        return '{}\nNo applicable rule'.format(U.highlight(self.ast, s))

no_op = lambda s, a: [(s, a)]

# type-checker acting on a set of checking rules
class Checker:
    def __init__(self, rules, return_type=T.TNone(), careful=False, ast_memo={}, memo={}):
        self.rules = rules
        self.return_type = return_type
        self.careful = careful
        # memoize past queries (remember which rules worked & the results they yielded)
        self.ast_memo = {}
        self.memo = {}

    def carefully(self):
        return Checker(
            self.rules,
            return_type = self.return_type,
            careful = True,
            ast_memo = self.ast_memo,
            memo = self.memo)

    def returning(self, r):
        return Checker(
            self.rules,
            return_type = r,
            careful = self.careful,
            ast_memo = self.ast_memo,
            memo = self.memo)

    # try each of the rules in order and run action corresponding to first matching rule
    # Checker * [Context] * AST * (Context * a -> [Context * b]) -> [Context * b]
    # fail with ConfusionError if no rules match
    # fail with CheckError if all rules that matched threw
    def analyze(self, Γs, ast, f = no_op):
        k_ast = P.simplify(ast)
        k = (ast, tuple(Γs))
        possible_errors = (ValueError, CheckError, ConfusionError, T.UnificationError)

        # compute results for each applicable pattern
        hits, a = self.memo[k] if k in self.memo else (0, None)
        options = []
        if isinstance(a, Exception):
            raise a
        if a is not None:
            options = a
            self.memo[k] = (hits + 1, options)
        else:
            if k_ast in self.ast_memo:
                ast_hits, matches = self.ast_memo[k_ast]
            else:
                ast_hits = 0
                matches = [(rule, a)
                    for rule in self.rules
                    for a in [P.matches(rule.pattern, ast)]
                    if a is not None]
            self.ast_memo[k_ast] = (ast_hits + 1, matches)

            options = []
            for Γ in Γs:
                errors = []
                for rule, match in matches:
                    try:
                        options.append((rule, rule.action(self, Γ.copy(), **match)))
                    except possible_errors as e:
                        errors.append((rule, e))
                if options == []:
                    e = ConfusionError(ast) if errors == [] else CheckError(ast, errors)
                    self.memo[k] = (1, e)
                    raise e
            self.memo[k] = (1, options)

        # run continuation with each result
        errors = []
        for rule, option in options:
            try:
                return [b for s, a in option for b in f(s, a)]
            except possible_errors as e:
                errors.append((rule, e))
        raise ConfusionError(ast) if errors == [] else CheckError(ast, errors)

    def check(self, ast):
        try:
            pairs = self.analyze([C.Context()], ast)
            state = C.State([s for s, _ in pairs])
            return U.verify(state)
        except (ValueError, CheckError, T.UnificationError) as e:
            if not self.careful and 'Unsatisfiable constraint' in str(e):
                self.carefully().check(ast)
            else:
                raise

    def dump_memo(self, s):
        for ast, (hits, rules) in sorted(self.ast_memo.items(), key=lambda a: a[1][0]):
            print('{}\n{} hits ({} rules)'.format(ast, hits, len(rules)))
        for (ast, Γs), (hits, _) in sorted(self.memo.items(), key=lambda a: a[1][0]):
            print('{}\n{} hits ({})'.format(U.highlight(ast, s), hits, type(ast).__name__))
            print('Contexts:')
            for c in Γs:
                print(str(c.reduced()))

# -------------------- rule/checker combinators --------------------

# given a pattern string s, and assumptions about the types of each capture group,
# return return_type
def expression(s, assumptions, return_type, name=None):
    to_type = lambda a: (T.parse(a) if type(a) is str else a)
    assumptions = dict((k, to_type(v)) for k, v in assumptions.items())
    return_type = to_type(return_type)
    def f(self, Γ, **kwargs):
        names = {v for _, t in assumptions.items() for v in t.names()} | return_type.names()
        def loop(Γ, pairs, analyzed):
            if pairs == []:
                # TODO better way of naming
                renaming = dict(zip(names, map(lambda a: 'tmp' + a, U.fresh_ids)))
                instantiate = lambda t: t.renamed(renaming).eapp()
                for name, inferred_type in analyzed:
                    Γ.unify(inferred_type, instantiate(assumptions[name]))
                return [(Γ, instantiate(return_type))]
            (name, ast), tail = pairs[0], pairs[1:]
            return self.analyze([Γ], ast, lambda new_Γ, inferred_type:
                loop(new_Γ, tail, analyzed + [(name, inferred_type)]))
        return loop(Γ, list(kwargs.items()), [])
    return Rule(s, f, name)

def literal(s, t, name=None):
    return Rule(s, lambda _, Γ: [(Γ, t)], name)

# binary infix operator op and corresponding variable type v and type constructor f
def binary_operator(op, v, f, name=None):
    return expression(
        '_a {} _b'.format(op), 
        {'a': v(T.parse('a')), 'b': v(T.parse('b'))},
        f(v(T.parse('a')), v(T.parse('b'))),
        name)

# extend an environment
def extend(self, Γ, bindings, k=no_op):
    c = Γ.copy()
    for a, t in bindings.items():
        t = T.parse(t)
        c.annotate(a, t)
    return k(c, None)

# -------------------- basic type-checking rules --------------------

def analyze_body(self, Γ, body, k=no_op):
    if body == []:
        return k(Γ, None)
    h, t = body[0], body[1:]
    return self.analyze([Γ], h, lambda new_Γ, _:
        analyze_body(self, (U.verify(new_Γ) if self.careful else new_Γ), t, k))

module = Rule(P.raw_pattern('__body'), analyze_body, 'module')

def analyze_cond(self, Γ, t, top, bot, k=no_op):
    top_Γ = Γ.copy().assume(t)
    bot_Γ = Γ.copy().assume(T.Not(t))
    top_results = analyze_body(self, top_Γ, top)
    bot_results = analyze_body(self, bot_Γ, bot)
    return [b
        for s, a in top_results + bot_results
        for b in k(s, a)]

cond = Rule('''
if _p:
    __top
else:
    __bot
''',
lambda self, Γ, p, top, bot:
    self.analyze([Γ], p, lambda new_Γ, t:
        analyze_cond(self, new_Γ, t, top, bot)),
'cond')

skip = Rule('pass', lambda self, Γ: [(Γ, None)], 'skip')

def analyze_cond_expr(self, Γ, t, l, r, k=no_op):
    top_Γ = Γ.copy().assume(t)
    bot_Γ = Γ.copy().assume(T.Not(t))
    top_results = self.analyze([top_Γ], l)
    bot_results = self.analyze([bot_Γ], r)
    return [b
        for s, a in top_results + bot_results
        for b in k(s, a)]

cond_expr = Rule(
    '_l if _p else _r',
    lambda self, Γ, l, p, r:
        self.analyze([Γ], p, lambda new_Γ, t:
            analyze_cond_expr(self, new_Γ, t, l, r)),
    'cond_expr')

def analyze_assign(self, Γ, lhs, rhs):
    assert type(lhs) is A.Name
    def k(new_Γ, new_t):
        if U.ident2str(lhs) in new_Γ:
            old_t = new_Γ.typeof(U.ident2str(lhs))
            if not (isinstance(old_t, T.AExp) and isinstance(new_t, T.AExp) or
                    isinstance(old_t, T.BExp) and isinstance(new_t, T.BExp)):
                new_Γ.unify(old_t, new_t)
        new_Γ.annotate(U.ident2str(lhs), new_t)
        return [(new_Γ, None)]
    return self.analyze([Γ], rhs, k)

assign = Rule('_lhs = _rhs', analyze_assign, 'assign')

def analyze_ident(self, Γ, a):
    return [(Γ, Γ.typeof(U.ident2str(a)))]

ident = Rule('a__Name', analyze_ident, 'ident')
attr_ident = Rule('a__Attribute', analyze_ident, 'attr_ident')

def analyze_fun_def(self, Γ, f, args, return_type, body):
    arg_types = []
    nested_Γ = Γ.copy()
    for arg in args:
        a, t = T.from_ast(arg)
        nested_Γ.annotate(a, t, fixed=True)
        arg_types.append(t)
    r = T.from_ast(return_type)
    arg_types = T.Tuple(arg_types) if len(arg_types) != 1 else arg_types[0]
    fun_type = T.Fun(arg_types, r)
    nested_Γ.annotate(f, fun_type, fixed=True)

    polymorphic_fun_type = fun_type.fresh(Γ.fixed)
    #print('fun_type =', fun_type)
    #print('polymorphic_fun_type =', polymorphic_fun_type)
    return analyze_body(
        self.returning(r),
        nested_Γ, body,
        lambda new_Γ, _: (lambda _:
            [(Γ.annotate(f, polymorphic_fun_type), None)])(U.verify(new_Γ)))

fun_def = Rule('''
def _f(__args) -> _return_type:
    __body''', analyze_fun_def, 'fun_def')

lit_None = literal('None', T.TNone())
lit_True = literal('True', T.BLit(True))
lit_False = literal('False', T.BLit(False))

bool_or = binary_operator('or', T.BVar, T.Or, 'bool_or')
bool_and = binary_operator('and', T.BVar, T.And, 'bool_and')
bool_not = expression('not _a', {'a': 'bool(a)'}, 'not bool(a)', 'bool_not')

lit_num = Rule('num__Num', lambda _, Γ, num:
    [(Γ, T.ALit(int(num.n)))], 'lit_num')
int_add = binary_operator('+', T.AVar, T.Add, 'int_add')
int_mul = binary_operator('*', T.AVar, T.Mul, 'int_mul')

ret = Rule('return _a', lambda self, Γ, a:
    self.analyze([Γ], a, lambda new_Γ, t:
        [(new_Γ.unify(self.return_type, t), None)]), 'return')

def analyze_fun_call(self, Γ, f, args):
    def loop(Γ, l, arg_types):
        if l == []:
            arg_type = T.Tuple(arg_types)
            def k(Γ, t):
                fresh_t = Γ.instantiate(t)
                a = fresh_t.a
                b = fresh_t.b
                #print(arg_type, '~', 'instantiate({}) = {}'.format(t.a, a))
                Γ.unify(arg_type, a)
                #print(
                #    '=>', b, '=', b.under(Γ),
                #    'after applying', P.pretty(P.explode(f)))
                #print(Γ)
                return [(Γ, b)]
            return self.analyze([Γ], f, k)
        h, t = l[0], l[1:]
        return self.analyze([Γ], h, lambda new_Γ, inferred_type:
            loop(new_Γ, t, arg_types + [inferred_type]))
    return loop(Γ, args, [])

fun_call = Rule('_f(__args)', analyze_fun_call, 'fun_call')

print_expr = expression('print(_a)', {'a': T.UVar('a')}, T.TNone(), 'print_expr')
print_stmt = Rule(
    P.raw_pattern('print(_a)').body[0],
    lambda self, Γ, a:
        self.analyze([Γ], a, lambda new_Γ, inferred_type:
            [(new_Γ, None)]))

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
        lambda self, Γ: extend(self, Γ, {
            'np.ones': 'Fun((int(a),), array[a])'}),
        'import_numpy')

    rules = basic_rules + [arr_zeros, add_row, smush, import_numpy]
    c = Checker(rules, return_type=T.parse('array[3]'))

    def try_check(s):
        c.careful = False
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

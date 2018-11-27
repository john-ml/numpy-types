from checker import *
from nptype import *
from context import *
import sys
import ast

if len(sys.argv) < 2:
    print('Usage: python3 numpycheck.py <file to check>')
    exit()

def numpy_rules(alias):
    P = lambda s: s.replace('np.', alias + '.')
    def all_overloads(f, n=5):
        c = 'a'
        s = [c]
        results = []
        for _ in range(n):
            results.extend(f(s))
            c = chr(ord(c) + 1)
            s.append(c)
        return results
    def binop(op, name):
        p = P('_a {} _b'.format(op))
        arr_type = lambda s: parse('array[{}]'.format(s))
        arg_types = lambda s: {'a': arr_type(s), 'b': arr_type(s)}
        same_dims = lambda s: [expression(p, arg_types(s), arr_type(s), '{}({})'.format(name, s))]
        fresh_int = lambda: AVar(TVar(next(fresh_ids)))
        scalar_broadcast = lambda s: [
            expression(p, {'a': fresh_int(), 'b': arr_type(s)}, arr_type(s),
                '{}({})_left_scalar'.format(name, s)),
            expression(p, {'a': arr_type(s), 'b': fresh_int()}, arr_type(s),
                '{}({})_right_scalar'.format(name, s))]
        return (all_overloads(lambda s: same_dims(', '.join(s))) +
                all_overloads(lambda s: scalar_broadcast(', '.join(s))))
    constructor = lambda name: all_overloads(lambda a: [
        expression(P('np.{}(({}))'.format(name, ', '.join('_' + b for b in a))),
            dict((v, AVar(TVar(v))) for v in a),
            parse('array[{}]'.format(', '.join(a))),
            '{}({})'.format(name, ', '.join(a)))])
    return (
        constructor('zeros') +
        constructor('ones') +
        binop('+', 'plus') +
        binop('-', 'minus') +
        binop('*', 'times') +
        binop('/', 'divide') +
        binop('**', 'pow'))

def analyze_import_numpy(self, context, np):
    self.rules += numpy_rules(np)
    return [(context, None)]

rules = basic_rules + [
    Rule(
        'import numpy as _np',
        analyze_import_numpy,
        'import_numpy'),
    Rule(
        'from nptyping import *',
        lambda self, context: [(context, None)],
        'nptyping')]

with open(sys.argv[1]) as f:
    s = f.read()
    try:
        Checker(rules).check(ast.parse(s))
        print('OK')
    except (CheckError, ConfusionError) as e:
        print(e.pretty(s))
    except Exception as e:
        print(e)

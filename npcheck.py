from checker import *
from nptype import *
from context import *
import util as U
import sys
import ast

if len(sys.argv) < 2:
    print('Usage: python3 numpycheck.py <file to check>')
    exit()

@typerule(globals())
def analyze_constructor(self, Γ, **kwargs):
    avars = dict(zip(kwargs, map(AVar, map(EVar, U.fresh_ids))))
    for k, e in shape, Γ <- kwargs.items():
        Γ, t <- self.analyze([Γ], e)
        Γ.unify(t, avars[k])
        yield t
    return [(Γ, Array(shape))]

@typerule(globals())
def analyze_binary_op(self, Γ, lhs, rhs):
    Γ, lhs_type <- self.analyze([Γ], lhs)
    Γ, rhs_type <- self.analyze([Γ], rhs)
    lhs_type = lhs_type.under(Γ)
    rhs_type = rhs_type.under(Γ)
    if type(lhs_type) is not Array:
        raise UnificationError(lhs_type, Array([UVar('a')]), 'expected array type')
    if type(rhs_type) is not Array:
        raise UnificationError(rhs_type, Array([UVar('a')]), 'expected array type')

    # check for arithmetic evar
    is_evar = lambda v: type(v) is AVar and type(a.var) is EVar

    # Broadcasting rules:
    # https://docs.scipy.org/doc/numpy-1.15.0/user/basics.broadcasting.html
    # - check dimensions in reverse order
    # - for each pair (a, b), need a = b \/ a = 1 \/ b = 1
    shape = []
    for l, r in zip(reversed(lhs_type), reversed(rhs_type)):
        # to avoid building up unnecessary z3 queries, only broadcast if 'obvious'
        eq_lr = l.to_z3() == r.to_z3()
        eq_l1 = l.to_z3() == 1
        eq_r1 = r.to_z3() == 1
        eq = eq_lr or eq_l1 or eq_r1
        if type(eq) is bool:
            if not eq:
                raise UnificationError(lhs_type, rhs_type, 'unbroadcastable dimensions')
            if eq_l1:
                shape.append(r)
            else:
                shape.append(l)
        else:
            Γ.unify(l, r)
            shape.append(l)

    longer_type = max([lhs_type, rhs_type], key=len)
    leftover_dims = longer_type[: -min(len(lhs_type), len(rhs_type))]
    shape = leftover_dims + shape[::-1]
    return [(Γ, Array(shape))]


# generate rules for numpy operations on all <=depth-dimensional arrays
def numpy_rules(alias, depth=4):

    # generate rules for array constructors np.zeros, np.ones, etc
    def constructor(name):
        arg = '_a' + next(U.fresh_ids)
        rules = [Rule(f'{alias}.{name}({arg})', analyze_constructor, f'{name}_base')]
        args = [arg]
        for i in range(1, depth + 1):
            rules.append(Rule(
                f'{alias}.{name}(({" ".join(a + "," for a in args)}))',
                analyze_constructor,
                f'{name}({", ".join(args)})'))
            args.append('_a' + next(U.fresh_ids))
        return rules

    # generate rules for binary operators on arrays with broadcastable dimensions
    def binary_ops(*ops):
        return [
            Rule(f'_lhs {op} _rhs', analyze_binary_op, f'array_{op}')
            for op in ops]

    # extracting dimensions of arrays w/ array.shape[k]
    @typerule(globals())
    def analyze_shape(self, Γ, a, i):
        Γ, ta <- self.analyze([Γ], a)
        if type(ta) is not Array:
            raise UnificationError(a, Array([AVar(UVar('a'))]), 'expected array type')
        i = i.n
        if i >= len(ta):
            raise ValueError(f'index {i} out of range of dimensions {ta}')
        return [(Γ, ta[i])]

    return (
        constructor('zeros') + constructor('ones') +
        binary_ops('+', '*', '-', '/', '**') +
        [Rule('_a.shape[i__Num]', analyze_shape)])

def analyze_import_numpy(self, context, np):
    self.rules = numpy_rules(np) + self.rules
    #for rule in self.rules:
    #    print(rule)
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

try:
    s = open(sys.argv[1]).read()
except FileNotFoundError:
    print(f'{sys.argv[1]}: No such file or directory')
    exit()

c = Checker(rules)
#state = c.check(ast.parse(s))
try:
    state = c.check(ast.parse(s))
    #print(state)
    print('OK')
except (CheckError, ConfusionError) as e:
    print(e.pretty(s))
except Exception as e:
    print(e)

#c.dump_memo(s)

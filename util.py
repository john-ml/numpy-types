from functools import *
indent = lambda space, s: '\n'.join(space + l for l in s.split('\n'))
typedict = lambda d: ', '.join('{} : {}'.format(k, v) for k, v in d.items())
union = lambda a, b: a | b
evars = lambda a: a.evars()
uvars = lambda a: a.uvars()
free_vars = lambda a: a.free_vars()
names_of = lambda a: a.names() if hasattr(a, 'names') else set()
to_z3 = lambda a: a.to_z3()
let = lambda a: a()
reducemap = lambda f, g, a, e: map(g, reduce(f, a, e))
mapreduce = lambda f, g, a, e: reduce(f, map(g, a), e)
on = lambda f, g: lambda a, b: f(g(a), g(b))
eq = lambda a, b: a == b
zipwith = lambda f, a: (f(l, r) for l, r in a)

def make_fresh():
    i = 0
    while True:
        yield 'fresh' + str(i)
        i += 1
fresh_ids = make_fresh()

def coords(ast):
    import ast as A
    row = ast.lineno - 1 if type(ast) is not A.Module else 0
    col = ast.col_offset if type(ast) is not A.Module else 0
    return row, col

def code_pointers(row, cols, s):
    return 'at {}:{}:\n{}\n{}'.format(
        row + 1,
        ','.join(str(a + 1) for a in sorted(cols)),
        s.split('\n')[row],
        ''.join(('^' if i in cols else ' ') for i in range(max(cols) + 1)))

def highlight(ast, s):
    row, col = coords(ast)
    return code_pointers(row, [col], s)

def ident2str(a):
    import ast as A
    if type(a) is A.Attribute:
        return '{}.{}'.format(ident2str(a.value), a.attr)
    elif type(a) is A.Name:
        return a.id
    elif type(a) is A.arg:
        return a.arg
    else:
        raise ValueError('Unknown AST node (ident2str): ', type(a))

def take(n, g):
    return map(lambda a: a[0], zip(g, range(n)))

def to_quantified_z3(a):
    import z3
    t = [b.to_z3() for b in a.uvars() & a.free_vars()]
    e = [b.to_z3() for b in a.evars() & a.free_vars()]
    #nats_t = z3.And([v >= 0 for v in t if type(v) is z3.ArithRef])
    #nats_e = z3.And([v >= 0 for v in e if type(v) is z3.ArithRef])
    #ex = z3.Exists(e, z3.Implies(nats_e, a.to_z3())) if len(e) > 0 else a.to_z3()
    #return z3.ForAll(t, z3.Implies(nats_t, ex)) if len(t) > 0 else ex
    ex = z3.Exists(e, a.to_z3()) if len(e) > 0 else a.to_z3()
    return z3.ForAll(t, ex) if len(t) > 0 else ex

def verify(a):
    import z3
    F = to_quantified_z3(a)

    #print('F =', str(F))
    #print('a =', str(a))

    s = z3.Solver()
    s.add(F)

    if s.check() != z3.sat:
        raise ValueError(
            'Unsatisfiable constraint: ' +
            str(F))

    return a

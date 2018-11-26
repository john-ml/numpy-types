from functools import *
typedict = lambda d: ', '.join('{} : {}'.format(k, v) for k, v in d.items())
union = lambda a, b: a | b
evars = lambda a: a.evars()
tvars = lambda a: a.tvars()
to_z3 = lambda a: a.to_z3()
let = lambda a: a()
reducemap = lambda f, g, a, e: map(g, reduce(f, a, e))
mapreduce = lambda f, g, a, e: reduce(f, map(g, a), e)
on = lambda f, g: lambda a, b: f(g(a), g(b))
eq = lambda a, b: a == b
zipwith = lambda f, a: (f(l, r) for l, r in a)
cant_unify = lambda a, b, reason='': \
    ValueError("Can't unify '{}' with '{}'{}".format( \
        a, b, ('' if reason == '' else ' ({})'.format(reason))))

def to_quantified_z3(a):
    import z3
    t = list(a.tvars())
    e = list(e.evars())
    ex = z3.Exists(e, a.to_z3()) if len(e) > 0 else a.to_z3()
    return z3.ForAll(t, ex) if len(t) > 0 else ex

def verify(a):
    import z3
    F = to_quantified_z3(state)

    s = z3.Solver()
    s.add(F)
    if s.check() != z3.sat:
        raise ValueError(
            'Unsatisfiable constraint: ' +
            str(F))

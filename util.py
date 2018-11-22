from functools import *
import z3
typedict = lambda d: ', '.join('{} : {}'.format(k, v) for k, v in d.items())
union = lambda a, b: a | b
evars = lambda a: a.evars()
tvars = lambda a: a.tvars()
to_z3 = lambda a: a.to_z3()
let = lambda a: a()
to_quantified_z3 = lambda a: \
    let(lambda t = tvars(a), e = evars(a): \
    let(lambda ex = (z3.Exists(e, to_z3(a)) if len(e) > 0 else to_z3(a)):
        z3.ForAll(t, ex) if len(t) > 0 else ex))
reducemap = lambda f, g, a, e: map(g, reduce(f, a, e))
on = lambda f, g: lambda a, b: f(g(a), g(b))
eq = lambda a, b: a == b
zipwith = lambda f, a: (f(l, r) for l, r in a)

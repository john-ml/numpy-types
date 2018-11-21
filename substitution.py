# union-find with path compression
# items should form partial order under compare
# if items are not comparable, assume they are equivalent and add equality constraint
# chooses smallest representative for each component
class Substitution:
    def __init__(self, compare):
        self.m = {}
        self.compare = compare
        self.equalities = set()
        self.bias = True

    def __str__(self):
        constraints = ', '.join(str(l) + ' ~ ' + str(r) for l, r in self.equalities)
        return '{' + ', '.join(str(k) + ' -> ' + str(v) for k, v in self.m.items()) + '}' + \
            (' where ' + constraints if constraints != '' else '')

    def find(self, a):
        traversed = []
        while a in self.m:
            traversed.append(a)
            a = self.m[a]
        for b in traversed:
            self.m[b] = a
        return a

    def union(self, a, b):
        self.bias = not self.bias
        a = self.find(a)
        b = self.find(b)
        if a == b:
            return self

        if self.compare(a, b):
            self.m[b] = a
        elif self.compare(b, a):
            self.m[a] = b
        else:
            self.m[[a, b][self.bias]] = [a, b][not self.bias]
            self.equalities |= {(a, b)}

        return self

    # convert equality constraints to z3 formula
    # assumes items implement .to_z3, .evars, .tvars
    # TODO: move this out of Substitution?
    def to_z3(self):
        from functools import reduce
        import z3
        concat = lambda g: list(map(lambda a: a.to_z3(), reduce(lambda a, b: a | b, g)))
        equalities = self.equalities | {(a, self.find(a)) for a in self.m}
        tvars = concat(l.tvars() | r.tvars() for l, r in equalities)
        evars = concat(l.evars() | r.evars() for l, r in equalities)
        equations = [l.to_z3() == r.to_z3() for l, r in equalities]
        return z3.ForAll(tvars, z3.Exists(evars, z3.And(equations)))

if __name__ == '__main__':
    σ = Substitution(lambda a, b: abs(a - b) < 0.5)
    σ.union(1, 2).union(3, 4).union(5, 6).union(7, 8) \
     .union(1, 3).union(5, 7) \
     .union(4, 8)
    print(σ)
    σ.union(1, 5.9)
    print(σ)

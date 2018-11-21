from z3 import *
p = Bool('p')
n = Int('n')
i = Int('i')

#print(simplify(ForAll([p, n], And(
#  Implies(p, And((1 + n) + 1 == (n + 1) + 1, (1 + n) + 1 == n + 2)),
#  Implies(Not(p), And(n + 1 == (n + 1) + 1, ((n + 1) + 1) + 1 == n + 2))))))

#solve(simplify(ForAll([i, p, n], And(
#  Implies(p, And(i == (1 + n), (1 + n) + 1 == (n + 1) + 1, i + 1 == n + 2)),
#  Implies(Not(p), And(i == (n + 1) + 1, n + 1 == (n + 1) + 1, i + 1 == n + 2))))))

# ∀ n, ∃ a b, 1 + n = b + 1 ∧ a + 1 = 1 + n ∧ b = a
a = Int('a')
b = Int('b')
solve(ForAll(n, Exists([a, b],
  And(True, 1 + n == b + 1, a + 1 == 1 + n, b == a))))

solve(And([a == b for a, b in [(1, 2), (3, 4)]]))

print({ ((n + 1) * n) : 0 }[(n + 1)*n])

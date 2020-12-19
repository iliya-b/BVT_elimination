from z3 import SolverFor, prove, Exists, BitVecs, And, Tactic, Int, Ints, Plus, Or, Implies

s = SolverFor('BV')
a, b, c, x, y = BitVecs('a b c x y', 9)
formula_orig = Exists(x, And(Exists(y, Or(x==y, x==a)), And(x==a, x==b)))


formula_dnf = a==b

prove(formula_orig == formula_dnf)




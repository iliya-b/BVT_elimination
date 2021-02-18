module Tests

open System
open BVTProver
open NUnit.Framework
open Microsoft.Z3
open BVTProver.Bvt
open BVTProver.BvtPatterns
open BvtElimination

let rec term_to_str (term: Expr) =
    match term with
        | Var name -> name.ToString()
        | Int num -> num.ToString()
        | Plus (a, Minus(Int 0, b)) -> "(" + (term_to_str a) + "-" + (term_to_str b) + ")"
        | Plus (a, b) -> "(" + (term_to_str a) + "+" + (term_to_str b) + ")"
        | Minus (Int 0, b) -> "(" + "-" + (term_to_str b) + ")"
        | Minus (a, b) -> "(" + (term_to_str a) + "-" + (term_to_str b) + ")"
        | Mult (a, b) -> "(" + (term_to_str a) + "*" + (term_to_str b) + ")"
        | expr -> expr.ToString()
        
let rec formula_to_str (formula: Expr): string =
    match formula with
        | CONJ args -> "And(" + String.Join(',', (Array.map (fun e -> formula_to_str e) args)) + ")" 
        | And (a, b) -> "And(" + formula_to_str(a)+", "+formula_to_str(b)+")" 
        | Or (a, b) -> "Or(" + formula_to_str(a)+", "+formula_to_str(b)+")"
        | True -> "True"
        | False -> "False"
        | Exists(name, F) -> "Exists(" + name.ToString() + ", " + (formula_to_str F) + ")"
        | Equals (t1, t2) ->  term_to_str(t1) + "==" + term_to_str(t2)
        | Le (t1, t2) ->  term_to_str(t1) + "<=" + term_to_str(t2)
        | Lt (t1, t2) ->  term_to_str(t1) + "<" + term_to_str(t2)
        | Ge (t1, t2) ->  term_to_str(t1) + ">=" + term_to_str(t2)
        | Gt (t1, t2) ->  term_to_str(t1) + ">" + term_to_str(t2)
        | Not t ->  "Not("+formula_to_str(t)+")"

[<SetUp>]
let Setup () =
    ()


[<Test>]
let TestEliminationProducesEquivalentFormula() =
    let x = ctx.MkBVConst("x", n)
    let y = ctx.MkBVConst("y", n)
    let a = ctx.MkBVConst("a", n)
    let b = ctx.MkBVConst("b", n)
    
    let formula = ctx.MkExists([|x|], ctx.MkAnd( ctx.MkExists([|y|], ctx.MkOr(ctx.MkEq(x, y), ctx.MkEq(x, a))), ctx.MkAnd(ctx.MkEq(x, a), ctx.MkEq(x, b) )))

    let eliminated_formula = EliminateAllQuantifiers formula -1
    
    let solver = ctx.MkSolver()
    solver.Add(ctx.MkNot(ctx.MkIff(formula, eliminated_formula)))
    
    Assert.AreEqual(solver.Check(), Status.UNSATISFIABLE)


[<Test>]
let TestNormalizationImpliesFormulaAndSatisfiedByItsModel () =
    let ctx = new Context()

    let n = 8u
    let x = ctx.MkBVConst("x", n)
    let y = ctx.MkBVConst("y", n)
    let c = ctx.MkBVConst("c", n)
    let z = ctx.MkBVConst("z", n)
    
    let bvt = BVT(ctx, n, 8)
    let (|=) = bvt.CHECK_MODEL
    let (=>) a b = ctx.MkImplies(a, b)
                    
    let (-*) = bvt.(-*)
    let (+*) = bvt.(+*)
    let (<=*) = bvt.(<=*)
        
    let f = c -* x +* y <=* z

    let model = Map.empty<Expr, Expr>.
                    Add(x, ctx.MkBV(9, n)).
                    Add(y, ctx.MkBV(255, n)).
                    Add(z, ctx.MkBV(80, n)).
                    Add(c, ctx.MkBV(84, n))
                    
    let rewritten = bvt.Rewrite f x model
    let s = ctx.MkSolver()
    s.Add(ctx.MkNot(rewritten => f))
    
    Assert.True(model |= f)
    Assert.True(model |= rewritten)
    Assert.AreEqual(s.Check(), Status.UNSATISFIABLE) // check rewritten => f
    printfn "%s => %s" (formula_to_str (rewritten)) (formula_to_str (f))
    
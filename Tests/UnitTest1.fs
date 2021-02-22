module Tests

open System
open BVTProver
open NUnit.Framework
open Microsoft.Z3
open BVTProver.Bvt
open BVTProver.Formula
open BvtElimination

[<SetUp>]
let Setup () =
    ()


[<Test>]
let TestEliminationProducesEquivalentFormula() =
    let x = Var "x"
    let y = Var "y"
    let a = Var "a"
    let b = Var "b"
    
    let formula = Exists(x, And([| Exists(y, Or([| (x===y); (x===a) |]) ) ; And ([| x===a; x===b |] ) |]))

    let eliminated_formula = EliminateAllQuantifiers formula
    0
//    let solver = ctx.MkSolver()
//    solver.Add(Not(Iff(formula, eliminated_formula)))
    
//    Assert.AreEqual(solver.Check(), Status.UNSATISFIABLE)


[<Test>]
let TestNormalizationImpliesFormulaAndSatisfiedByItsModel () =
    let ctx = new Context()
    
    let n = 8u
    let x = Var "x"
    let y = Var "y"
    let c = Var "c"
    let z = Var "z"
    
    let bvt = BVT(ctx, n, 8)
                        
    let f = c - x + y <== z
    

    let model = Map.empty<string, int>.
                    Add("x", 9).
                    Add("y", 255).
                    Add("z", 80).
                    Add("c", 84)
                    
    let rewritten = bvt.Rewrite f x model 0
    
    
    printfn "%O" f
    printfn "%O" rewritten
    
    let checker = Not(rewritten => f)
    let s = ctx.MkSolver()
    let X = ctx.MkBVConst("x", 8u)
    let Y = ctx.MkBVConst("y", 8u)
//    s.Add(ctx.MkNot(ctx.MkEq(ctx.MkBVSub(X, Y), ctx.MkBVAdd(X, ctx.MkBVNeg(Y))) ))
//    Assert.AreEqual(Status.UNSATISFIABLE, s.Check()) // check rewritten => f

    let zf = checker.z3 ctx

    s.Add(zf)

    Assert.True(model |= f)
    Assert.True(model |= rewritten)
    Assert.AreEqual(Status.UNSATISFIABLE, s.Check()) // check rewritten => f


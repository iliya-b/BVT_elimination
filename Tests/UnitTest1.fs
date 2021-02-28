module Tests

open System
open BVTProver
open NUnit.Framework
open Microsoft.Z3
open BVTProver.Bvt
open BVTProver.Formula
open BvtElimination
open Mbp

[<SetUp>]
let Setup () =
    ()


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
    
[<Test>]
let TestMbpInterpolatesTheFormula () =
    let model = Map.empty<string, int>.
                        Add("a", 10).
                        Add("b", 100).
                        Add("x", 5)
    
    let x = Var "x"
    let a = Var "a"
    let b = Var "b"
    
    let cube = [| a <! (Int 4)*x ; (Int 6)*x <== b |]
    let f = MbpZ model x (Cube cube)
    Assert.AreEqual(3, f.conjuncts.Length)
    Assert.Contains(Le (Var "a",Int 85), f.conjuncts)
    Assert.Contains(Le (Var "b",Int 127), f.conjuncts)
    Assert.Contains(Lt (Div (Mult (Var "a",Int 3),12),Div (Mult (Var "a",Int 3),12)), f.conjuncts)
    // todo: not rely on order of arguments in commuting operations
    printfn "%A" f.conjuncts
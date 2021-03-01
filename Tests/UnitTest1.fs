module Tests.Mbp

open System
open BVTProver
open Microsoft.Z3
open NUnit.Framework
open Microsoft.Z3
open BVTProver.Bvt
open BVTProver.Formula
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
                    
    let rewritten = And(Array.ofList (bvt.Rewrite f x model 0))
    
    
    printfn "%O" f
    printfn "%O" rewritten
    
    let s = ctx.MkSolver()
    let zf = Not(rewritten => f).z3 ctx
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
    
    let ctx = new Context();
    
    let cube = [| a <! 4*x ; 6*x <== b |] // a < 4x ∧ 6x < b
    let mbp = MbpZ model x (Cube cube)
    Assert.False(mbp.as_formula.contains x)
    
    Assert.AreEqual(3, mbp.conjuncts.Length)
    Assert.Contains(Le (Var "a",Int 85), mbp.conjuncts)
    Assert.Contains(Le (Var "b",Int 127), mbp.conjuncts)
    Assert.Contains(Lt (Div (Mult (Var "a",Int 3),12),Div (Mult (Var "a",Int 3),12)), mbp.conjuncts)
    // todo: not rely on order of arguments in commuting operations
    printfn "%A" mbp.conjuncts
    
    // check that MBP⇒∃x.f
    let expected = Implies(And(mbp.conjuncts), Exists(x, And cube))
    let solver = ctx.MkSolver()
    solver.Add(Not(expected).z3 ctx)
    Assert.AreEqual(solver.Check(), Status.UNSATISFIABLE)
    
[<Test>]
let TestMbpKeepsFreeConjunct () =
    let x, a, b = Var "x", Var "a", Var "b"
    
    let model = Map.empty<string, int>.
                        Add("a", 0).
                        Add("b", 200).
                        Add("x", 1)
    let f = x
    let free_conjunct = 100*a <== b
    
    let cube = Cube ([| Div (f, 3) <== b; free_conjunct |])
    
    let rew = MbpZ model x cube
    
    Assert.Contains(free_conjunct, rew.conjuncts)
    
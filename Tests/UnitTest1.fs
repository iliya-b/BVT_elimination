module Tests.Mbp

open BVTProver
open BVTProver
open Microsoft.Z3
open NUnit.Framework

open BVTProver.Formula
open Mbp
open FormulaActions
open Bvt

[<SetUp>]
let Setup () =
    ()


[<Test>]
let TestNormalizationImpliesFormulaAndSatisfiedByItsModel () =
    let ctx = new Context()
    let x = Var "x"
    let y = Var "y"
    let c = Var "c"
    let z = Var "z"
                            
    let f = c - x + y <== z
    

    let model = dict ["x", 9u ; "y", 255u ; "z", 80u ; "c", 84u]
                    
    let rewritten = And(Rewrite x model f)
    
    
    printfn "%O" f
    printfn "%O" rewritten
    
    let s = ctx.MkSolver()
    let zf = z3fy_formula ctx (Not (rewritten => f))
    s.Add(zf)

    Assert.True(model |= f)
    Assert.True(model |= rewritten)
    Assert.AreEqual(Status.UNSATISFIABLE, s.Check()) // check rewritten => f
    
    
[<Test>]
let TestMbpInterpolatesTheFormula () =
    let model = dict [ "a", 10u ; "b", 100u ; "x", 5u ]
    
    let x = Var "x"
    let a = Var "a"
    let b = Var "b"
    
    let ctx = new Context();
    
    let cube = [ a <! 4u*x ; 6u*x <== b ] // a < 4x ∧ 6x < b
    let mbp = MbpZ model x cube
    Assert.False(formula_contains x (And mbp))
    
    Assert.AreEqual(3, mbp.Length)
    Assert.True(List.contains (Le (Var "a",Int 85u)) mbp)
    Assert.True(List.contains (Le (Var "b",Int 127u)) mbp)
    Assert.True(List.contains (Lt (Div (Mult (Var "a",Int 3u), Int 12u),Div (Mult (Var "a",Int 3u), Int 12u))) mbp)
    // todo: not rely on order of arguments in commuting operations
    printfn "%A" mbp
    
    // check that MBP⇒∃x.f
    let expected = Implies((And mbp), Exists(x, And cube))
    let solver = ctx.MkSolver()
    solver.Add(z3fy_formula ctx (Not expected))
    Assert.AreEqual(solver.Check(), Status.UNSATISFIABLE)
    
[<Test>]
let TestMbpKeepsFreeConjunct () =
    let x, a, b = Var "x", Var "a", Var "b"
    
    let model = dict [ "a", 0u ; "b", 200u ; "x", 1u ]
    
    let f = x
    let free_conjunct = 100u*a <== b
    
    let cube = [ Div (f, Int 3u) <== b; free_conjunct ]
    
    let rew = MbpZ model x cube
    
    Assert.True(List.contains free_conjunct rew)
    
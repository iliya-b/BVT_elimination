module Tests.Mbp

open BVTProver
open Microsoft.Z3
open NUnit.Framework

open BVTProver.Formula
open Mbp
open FormulaActions
open Bvt
open Interpreter

[<SetUp>]
let Setup () =
    ()


[<Test>]
let TestNormalizationImpliesFormulaAndSatisfiedByItsModel () =
    let bit_len = 8u
    let Rewrite = Rewrite bit_len
    let ctx = new Context()
    let x = Var ("x", bit_len)
    let y = Var ("y", bit_len)
    let c = Var ("c", bit_len)
    let z = Var ("z", bit_len)
                            
    let f = c - x + y <== z
    

    let model = dict ["x", 9u ; "y", 255u ; "z", 80u ; "c", 84u]
                    
    let rewritten_conjuncts = Rewrite x model f
    
    
    printfn "%O" f
    printfn "%A" rewritten_conjuncts
    
    let s = ctx.MkSolver()
    let zf = z3fy_expression ctx (Formula (Not (And rewritten_conjuncts => f)))
    s.Add(zf :?> BoolExpr)

    Assert.True(model |= f)
    Assert.True(List.forall ((|=) model) rewritten_conjuncts)
    Assert.AreEqual(Status.UNSATISFIABLE, s.Check()) // check rewritten => f
    
    
[<Test>]
let TestMbpInterpolatesTheFormula () =
    let model = dict [ "a", 10u ; "b", 100u ; "x", 5u ]
    let bit_len = 8u
    let x = Var ("x", bit_len)
    let a = Var ("a", bit_len)
    let b = Var ("b", bit_len)
    let Int = Int bit_len
    
    let ctx = new Context();
    
    let cube = [ a <! (Int 4u)*x ; (Int 6u)*x <== b ] // a < 4x ∧ 6x < b
    let mbp = MbpZ model x bit_len cube
    Assert.False (formula_contains x (And mbp))
    
    Assert.AreEqual(3, mbp.Length)
    Assert.True(List.contains (Le (Var ("a", 8u),Int 85u)) mbp)
    Assert.True(List.contains (Le (Var ("b", 8u),Int 127u)) mbp)
    Assert.True(List.contains (Lt (Div (Mult (Var ("a", 8u),Int 3u), Int 12u),Div (Mult (Var ("a", 8u),Int 3u), Int 12u))) mbp)
    // todo: not rely on order of arguments in commuting operations
    printfn "%A" mbp
    
    // check that MBP⇒∃x.f
    let expected = Implies(And mbp, Exists(x, And cube))
    let solver = ctx.MkSolver()
    let not_expected = z3fy_expression ctx (Formula (Not expected))
    solver.Add(not_expected :?> BoolExpr)
    Assert.AreEqual(solver.Check(), Status.UNSATISFIABLE)
    
[<Test>]
let TestMbpKeepsFreeConjunct () =
    let bit_len = 8u
    let Int = Int bit_len
    let x, a, b = Var ("x", bit_len), Var ("a", bit_len), Var ("b", bit_len)
    
    let model = dict [ "a", 0u ; "b", 200u ; "x", 1u ]
    
    let f = x
    let free_conjunct = (Int 100u)*a <== b
    
    let cube = [ Div (f, Int 3u) <== b; free_conjunct ]
    
    let rew = MbpZ model x bit_len cube
    
    Assert.True(List.contains free_conjunct rew)
    
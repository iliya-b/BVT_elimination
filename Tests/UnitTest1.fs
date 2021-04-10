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

    let x = ("x", bit_len)
    let y = ("y", bit_len)
    let c = ("c", bit_len)
    let z = ("z", bit_len)
                            
    let f = Var c - Var x + Var y <== Var z
    

    let model = dict [x, 9u ; y, 255u ; z, 80u ; c, 84u]
                    
    let rewritten_conjuncts = Rewrite x model f
    Assert.IsTrue (rewritten_conjuncts.IsSome)
    let rewritten_conjuncts = rewritten_conjuncts.Value
    
    printfn "%O" f
    printfn "%A" rewritten_conjuncts
    
    Assert.False (is_tautology ((And rewritten_conjuncts <=> f)))
    Assert.True (is_tautology (And rewritten_conjuncts => f))
    Assert.True(model |= f)
    Assert.True(model |= (And rewritten_conjuncts))
    
    
[<Test>]
let TestMbpInterpolatesTheFormula () =
    let bit_len = 8u
    let x = ("x", bit_len)
    let a = ("a", bit_len)
    let b = ("b", bit_len)
    let Int = Int bit_len
    let model = dict [ a, 10u ; b, 100u ; x, 5u ]

    let cube = [ Var a <! (Int 4u) * Var x ; (Int 6u) * Var x <== Var b ] // a < 4x ∧ 6x < b

        
    let mbp = MbpZ model x cube
    Assert.False (formula_contains (Var x) (And mbp))
    
    Assert.AreEqual(3, mbp.Length)
    Assert.True(List.contains (Le (Var ("a", 8u), Int 85u)) mbp)
    Assert.True(List.contains (Le (Var ("b", 8u), Int 127u)) mbp)    
    // check that MBP⇒∃x.f
    let expected_1 = Implies(And mbp, Exists(Var x, And cube))

    Assert.True (is_tautology expected_1)
    Assert.AreEqual(["((a*3) div 12)<((b*2) div 12)"; "a<=85"; "b<=127"], List.map (fun x -> x.ToString()) mbp)
    
    
[<Test>]
let TestMbpKeepsFreeConjunct () =
    let bit_len = 8u
    let Int = Int bit_len
    let x, a, b = ("x", bit_len), ("a", bit_len), ("b", bit_len)
    
    let model = dict [ a, 0u ; b, 200u ; x, 1u ]
    
    let f = x
    let free_conjunct = (Int 100u) * Var a <== Var b
    
    let cube = [ Div (Var f, Int 3u) <== Var b; free_conjunct ]
    
    let rew = MbpZ model x cube
    
    Assert.True(List.contains free_conjunct rew)
    
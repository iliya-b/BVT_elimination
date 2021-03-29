module Tests.Rules

open BVTProver
open NUnit.Framework
open BVTProver.Formula
open RewriteRules.Rule2
open RewriteRules.Rule3
[<SetUp>]
let Setup () =
    ()


[<Test>]
let TestRule2ByPassesWhenLcmOverflows () =
    let bit_len = 8u
    let x, a, b = Var ("x", bit_len), Var ("a", bit_len), Var ("b", bit_len)
    let Int = Int bit_len
    
    let model = [ "a", 0u
                  "b", 200u
                  "x", 1u ] |> dict
    
    let cube = [ a <! (Int 99u)*x ; (Int 100u)*x <== b ]
    match cube with
    | Rule2 model "x" bit_len bounds -> Assert.Fail()
    | t -> ignore t

    
[<Test>]
let TestRule3 () =
    let bit_len = 8u
    let Int = Int bit_len
    let x, a, b = Var ("x", 8u), Var ("a", 8u), Var ("b", 8u)
    
    let model = [ "a", 0u
                  "b", 4u
                  "x", 1u ] |> dict
    let f = x
    let free_conjunct = (Int 100u)*a <== b
    let upper_bound = Div (f, Int 3u) <== b
    let cube = [ upper_bound; free_conjunct ]
    
    match cube with
    | Rule3 model "x" bit_len conjunct ->
        Assert.AreEqual(conjunct, upper_bound)
        let rewritten = apply_rule3 model "x" bit_len conjunct

        Assert.True(List.contains (Le(b, Div(Int 255u, Int 3u))) rewritten)
        Assert.True(List.contains (Le(x, (Mult(Plus(b, (Int 1u)), Int 3u)-(Int 1u)))) rewritten)
    
    | _ -> Assert.Fail()
    
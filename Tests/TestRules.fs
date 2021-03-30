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
    let x, a, b = ("x", bit_len), ("a", bit_len), ("b", bit_len)
    let Int = Int bit_len
    
    let model = [ "a", 0u
                  "b", 200u
                  "x", 1u ] |> dict
    
    let cube = [ Var a <! (Int 99u) * Var x ; (Int 100u) * Var x <== Var b ]
    match cube with
    | Rule2 model x bounds -> Assert.Fail()
    | t -> ignore t

    
[<Test>]
let TestRule3 () =
    let bit_len = 8u
    let Int = Int bit_len
    let x, a, b = ("x", 8u), ("a", 8u), ("b", 8u)
    
    let model = [ "a", 0u
                  "b", 4u
                  "x", 1u ] |> dict
    let f = x
    let free_conjunct = (Int 100u) * Var a <== Var b
    let upper_bound = Div (Var f, Int 3u) <== Var b
    let cube = [ upper_bound; free_conjunct ]
    
    match cube with
    | Rule3 model x conjunct ->
        Assert.AreEqual(conjunct, upper_bound)
        let rewritten = apply_rule3 model x conjunct

        Assert.True(List.contains (Le(Var b, Div(Int 255u, Int 3u))) rewritten)
        Assert.True(List.contains (Le(Var x, (Mult(Plus(Var b, (Int 1u)), Int 3u)-(Int 1u)))) rewritten)
    
    | _ -> Assert.Fail()
    
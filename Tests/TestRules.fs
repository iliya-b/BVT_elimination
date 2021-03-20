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
let TestRule2ByPassesWhenLcmOverflows =
    let x, a, b = Var "x", Var "a", Var "b"
    
    let model = [ "a", 0u
                  "b", 200u
                  "x", 1u ] |> dict
    
    let cube = [ a <! 99u*x ; 100u*x <== b ]
    match cube with
       | Rule2 model x bounds -> Assert.Fail()
       | t -> ignore t

    
[<Test>]
let TestRule3 () =
    let x, a, b = Var "x", Var "a", Var "b"
    
    let model = [ "a", 0u
                  "b", 4u
                  "x", 1u ] |> dict
    let f = x
    let free_conjunct = 100u*a <== b
    let upper_bound = Div (f, Int 3u) <== b
    let cube = [ upper_bound; free_conjunct ]
    
    match cube with
    | Rule3 model x conjunct ->
        Assert.AreEqual(conjunct, upper_bound)
        let rewritten = apply_rule3 model x conjunct

        Assert.True(List.contains (Le(b, Div(Int 255u, Int 3u))) rewritten)
        Assert.True(List.contains (Le(x, (Mult(Plus(b, Term.One), Int 3u)-Term.One))) rewritten)
    
    | _ -> Assert.Fail()
    
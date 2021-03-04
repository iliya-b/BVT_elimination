module Tests.Rules

open System
open BVTProver
open Microsoft.Z3
open NUnit.Framework
open Microsoft.Z3
open BVTProver.Bvt
open BVTProver.Formula
open BVTProver.FormulaActions
open RewriteRules.Rule2
open RewriteRules.Rule3
open RewriteRules.Rule3

[<SetUp>]
let Setup () =
    ()


[<Test>]
let TestRule2ByPassesWhenLcmOverflows =
    let x, a, b = Var "x", Var "a", Var "b"
    
    let model = [ "a", 0
                  "b", 200
                  "x", 1 ] |> Map.ofList
    
    let cube = [ a <! 99*x ; 100*x <== b ]
    match cube with
       | Rule2 model x bounds -> Assert.Fail()
       | t -> ignore t

    
[<Test>]
let TestRule3 () =
    let x, a, b = Var "x", Var "a", Var "b"
    
    let model = [ "a", 0
                  "b", 4
                  "x", 1 ] |> Map.ofList
    let f = x
    let free_conjunct = 100*a <== b
    let upper_bound = Div (f, 3) <== b
    let cube = [ upper_bound; free_conjunct ]
    
    match cube with
    | Rule3 model x conjunct ->
        Assert.AreEqual(conjunct, upper_bound)
        let rewritten = apply_rule3 model x conjunct

        Assert.True(List.contains (Le(b, Div(Int 255, 3))) rewritten)
        Assert.True(List.contains (Le(x, (Mult(Plus(b, Term.One), Int 3)-Term.One))) rewritten)
    
    | _ -> Assert.Fail()
    
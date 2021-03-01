module Tests.Rules

open System
open BVTProver
open Microsoft.Z3
open NUnit.Framework
open Microsoft.Z3
open BVTProver.Bvt
open BVTProver.Formula
open RewriteRules.Rule2
open RewriteRules.Rule3
open RewriteRules.Rule3

[<SetUp>]
let Setup () =
    ()


[<Test>]
let TestRule2ByPassedWhenLcmOverflows =
    let x, a, b = Var "x", Var "a", Var "b"
    
    let model = Map.empty<string, int>.
                        Add("a", 0).
                        Add("b", 200).
                        Add("x", 1)
    let cube = Cube ([| a <! 99*x ; 100*x <== b |])
    match cube with
       | Rule2 model x (lcm, bounds) -> Assert.Fail()
       | t -> ignore t

    
[<Test>]
let TestRule3 () =
    let x, a, b = Var "x", Var "a", Var "b"
    
    let model = Map.empty<string, int>.
                        Add("a", 0).
                        Add("b", 4).
                        Add("x", 1)
    let f = x
    let free_conjunct = 100*a <== b
    let upper_bound = Div (f, 3) <== b
    let cube = Cube ([| upper_bound; free_conjunct |])
    
    match cube with
    | Rule3 model x (Upper_(t1, num, t2), conjunct) ->
        Assert.AreEqual(conjunct, upper_bound)
        Assert.AreEqual(t1, f)
        Assert.AreEqual(num, 3)
        Assert.AreEqual(t2, b)
    | _ -> Assert.Fail()
    
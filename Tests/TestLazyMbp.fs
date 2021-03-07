module Tests.TestLazyMbp

open BVTProver
open NUnit.Framework
open BVTProver.Formula
open Mbp
[<SetUp>]
let Setup () =
    ()


[<Test>]
let TestLAzy () =
    let a, b, x = Var "a", Var "b", Var "x"
    let f = [a <== x ; x <! b; Extract(x, 7, 7)===Term.Zero]
    let M = [ "x", 64 ] |> Map.ofList
    let rew = LazyMbp M x f
    printfn "%O" (And rew)
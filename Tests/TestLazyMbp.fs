module Tests.TestLazyMbp

open BVTProver
open Microsoft.Z3
open NUnit.Framework
open BVTProver.Formula
open FormulaActions
open Mbp
[<SetUp>]
let Setup () =
    ()


[<Test>]
let TestLAzy () =
    let a, b, x = Var "a", Var "b", Var "x"
    let f = [a <== x ; x <! b; Extract(x, 7, 7)===Term.Zero]
    let M = [ "x", 64u ] |> dict
    let rew = LazyMbp M x f
    printfn "%O" (And rew)

[<Test>]
let TestBenchmark() =
    let ctx = new Context()
    let file = "/Volumes/MyPassport/bvt/samples/bench_10.smt2.txt"
    let fs = ctx.ParseSMTLIB2File(file)
    let solver = ctx.MkSolver()
    solver.Add(fs)
    let s = solver.Check()
    
    let ss = Array.map formula_from_z3 fs
//    let back = Array.map (z3fy_formula ctx) ss
    printf "formula: %A" ss
    printf "model: %s" (solver.Model.ToString())
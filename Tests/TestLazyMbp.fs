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
    let a, b, x = Var ("a", 8u), Var ("b", 8u), Var ("x", 8u)
    let f = [a <== x ; x <! b; Extract(x, 7, 7)===Term.Zero]
    let M = [ "x", 64u ] |> dict
    let rew = LazyMbp M x f
    printfn "%O" (And rew)

[<Test>]
let TestBenchmark() =
    let ctx = new Context()
    let file = "/Volumes/MyPassport/bvt/samples/bench_10.smt2.txt"
    let fs = ctx.ParseSMTLIB2File(file)
       
    let ss = Array.map convert_z3 fs
    let zz = Array.map (z3fy_expression ctx) ss
//    let back = Array.map (z3fy_formula ctx) ss

    
    let solver = ctx.MkSolver()
    solver.Add(ctx.MkNot(ctx.MkIff(zz.[44] :?> BoolExpr, fs.[44])))
    let s = solver.Check()
    
    printf "formula: %O %O" zz.[44] fs.[44]
    printf "model: %s" (solver.Model.ToString())
module Tests.TestLazyMbp

open System
open System.Collections
open BVTProver
open Microsoft.Z3
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
    let benchmark_formulae = ctx.ParseSMTLIB2File(file)
   
    let our_formulae = Array.map (convert_z3>>(z3fy_expression ctx)) benchmark_formulae
    
    let test_iff (a: Expr) (b: Expr) =
        let solver = ctx.MkSolver()
        solver.Add(ctx.MkNot(ctx.MkIff(a :?> BoolExpr, b :?> BoolExpr)))
        let s = solver.Check()
        s=Status.UNSATISFIABLE
    let ok = Array.forall2 test_iff benchmark_formulae our_formulae
    
    Assert.True ok
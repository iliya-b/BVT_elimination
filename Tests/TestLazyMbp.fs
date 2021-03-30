module Tests.TestLazyMbp


open System
open System.Collections.Generic
open System.IO
open System.Linq.Expressions
open BVTProver
open Microsoft.Z3

open NUnit.Framework
open BVTProver.Formula
open FormulaActions
open Mbp
open Substitution
open Helpers

[<SetUp>]
let Setup () =
    ()


[<Test>]
let TestLazyMbpProducesAnApproximation () =
    let bit_len = 8u
    let a, b, x = ("a", bit_len), ("b", bit_len), ("x", bit_len)
    let Zero = Int 1u 0u
    let f = [Var a <== Var x ; Var x <! Var b; Extract(Var x, 7, 7)===Zero]
    let M = [ "x", 64u ; "a", 199u ; "b", 200u ] |> dict
    let lazy_mbp = LazyMbp M x f
    printfn "%O" (And lazy_mbp)

    let naive_mbp = List.map (substitute_formula (dict ["x", Int 8u 64u])) f
    
    (* check that at least one rule is used *)
    Assert.False (is_tautology (And lazy_mbp <=> And naive_mbp)) 
    Assert.True (is_tautology (And lazy_mbp => Exists(Var x, And f)))
    

[<Test>]
let TestBenchmarkConverting() =
    let ctx = new Context()
    let file = "./bvt/samples/bench_10.smt2.txt"
    let solver = ctx.MkSolver() 

    let benchmark_formulae = ctx.ParseSMTLIB2File(file)
    let our_formulae = Array.map (convert_z3>>(z3fy_expression ctx)) benchmark_formulae
    
    let test_iff (a: Expr) (b: Expr) =
        solver.Reset ()
        solver.Add (ctx.MkNot(ctx.MkIff(a :?> BoolExpr, b :?> BoolExpr)))
        let s = solver.Check ()
        s=Status.UNSATISFIABLE
        
    let ok = Array.forall2 test_iff benchmark_formulae our_formulae
    
    Assert.True ok
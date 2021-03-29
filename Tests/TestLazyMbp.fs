module Tests.TestLazyMbp


open System
open System.Collections.Generic
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
let TestLAzy () =
    let bit_len = 8u
    let a, b, x = Var ("a", bit_len), Var ("b", bit_len), Var ("x", bit_len)
    let Zero = Int 1u 0u
    let f = [a <== x ; x <! b; Extract(x, 7, 7)===Zero]
    let M = [ "x", 64u ; "a", 199u ; "b", 200u ] |> dict
    let lazy_mbp = LazyMbp M x bit_len f
    
    let naive_mbp = List.map (substitute_formula (dict ["x", Int 8u 64u])) f
    Assert.False(is_tautology (And lazy_mbp <=> And naive_mbp)) // check that at least one rule is used
    Assert.True(is_tautology (And lazy_mbp => Exists(x, And f)))
    
    printfn "%O" (And lazy_mbp)

[<Test>]
let TestMbpOnBenchmark() =
    let ctx = new Context()
    let file = "/Volumes/MyPassport/bvt/samples/bench_10.smt2.txt"
    
    let benchmark_formulae = Array.take 10 (ctx.ParseSMTLIB2File file)
    let to_formula = function | Formula f -> f | _ -> unexpected ()
    
    
    let test = ctx.MkBVULE (ctx.MkBV(8u, 3u), ctx.MkBV(2u, 3u))
    
    let our_formulae = Array.map (convert_z3>>to_formula) benchmark_formulae
    
    
    let convert_const (z3_const: KeyValuePair<FuncDecl, Expr>) =
        let key, value = z3_const.Key, z3_const.Value :?> BitVecNum
        key.Name.ToString(), value.UInt
        
    let createMbp f =
        let model = get_model f
        Assert.True model.IsSome
        let model = model.Value.Consts |> (Seq.map convert_const) |> dict
        model
//        let mbp = LazyMbp model x f
//        mbp
    let m = (Array.map createMbp our_formulae)
    Assert.True true

[<Test>]
let TestBenchmarkConverting() =
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
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
    


//[<Test>]
//let TestMbpOnBenchmark() =
//    let ctx = new Context()
//
//    let has_lia_Literal (file: string) = 
//        let file = "/Volumes/MyPassport/bvt/QF_BV/" + ((file.Split ":").[0])
//        
//        let benchmark_formulae = (ctx.ParseSMTLIB2File file)
//        let to_formula = function | Formula f -> f | _ -> unexpected ()
//        
//        let ignore_exception f e =
//            try
//                f e
//            with
//            | :? System.Exception as e -> False
//            
//        let our_formulae = Array.map ( ignore_exception (convert_z3>>to_formula)) benchmark_formulae
//        
//        
//        let convert_const (z3_const: KeyValuePair<FuncDecl, Expr>) =
//            let key, value = z3_const.Key, z3_const.Value :?> BitVecNum
//            Var (key.Name.ToString(), value.SortSize), Integer (value.UInt, value.SortSize)
//        
//        Array.tryFind is_LIA_formula our_formulae
//    
//    let lia = Array.ofSeq (Seq.take 100 (Seq.choose has_lia_Literal (files.Split "\n")))
//    
//    Assert.True true

//    Assert.True true

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
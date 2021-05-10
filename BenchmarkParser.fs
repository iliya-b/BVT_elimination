module BVTProver.BenchmarkParser


open System
open System.Collections.Generic
open System.Diagnostics
open System.IO
open BVTProver
open BVTProver.RewriteRules
open Helpers
open Formula
open FormulaActions
open Interpreter
open Bvt
open Mbp
open Microsoft.Z3
open Z3Patterns
open Microsoft.Z3
open Mbp
open Rule3

open System
open System.IO
let private extract_num  (e: KeyValuePair<FuncDecl, Expr>) =
    match e.Value with
    | :? BitVecNum as e -> Some e
    | _ -> None
    
    
// good: /Volumes/MyPassport/bvt/QF_BV/2018-Goel-hwbench/QF_BV_bv_bv_eq_sdp_v5_cc_ref_max.smt2
let private is_some_lia_conjuncts i path =
    async {
        if path="/Volumes/MyPassport/bvt/QF_BV/2019-Mann/ridecore-qf_bv-bug.smt2" then
            return (path, 0)
        else 
            let ctx = new Context()
            let j = i
           
           
            let benchmark_formulae = ctx.ParseSMTLIB2File(path)
            
            let arithmetic_part = benchmark_formulae |> Array.filter is_LIA_z3
            let depth = Array.map (z3_depth_formula 0) arithmetic_part
            if Array.length depth = 0 then
                return (path, 0)
            else
                return (path, Array.max depth)
    }



     
let is_bv_model (model: Model) =
    Seq.forall (fun (e: KeyValuePair<FuncDecl, Expr>) -> e.Value.IsBV) model.Consts      


        
let  get_model_z3_many (ctx: Context) (expr: BoolExpr[]) =    
    let solver = ctx.MkSolver()
    solver.Set("timeout", 2000u) // todo make configurable
    solver.Add (expr)
    if solver.Check()=Status.SATISFIABLE then
        Some solver.Model
    else
        None
        
let doLazyMbp (ctx: Context) (model: Model) benchmark_formulae =
        
    let is_tautology_z3 = is_tautology_z3 ctx
        
    
    if Seq.exists (extract_num>>Option.isNone) model.Consts then
                        false // if some variable is not in BVT (e.g. a propositional var)
    else
                        
                        let inline And (fs: BoolExpr list) = fs |>  List.map (function | :? BoolExpr as e -> e | _ -> unexpected ()) |> Array.ofList |> ctx.MkAnd 
                        let inline exists x f = ctx.MkExists([| x |], f)
                        let inline (=>.) f1 f2 = ctx.MkImplies(f1, f2)
                        let inline (<=>.) f1 f2 = ctx.MkIff(f1, f2)
                        
                        let x = model.ConstDecls.[0]
                        let benchmark_formulae = List.ofArray benchmark_formulae
                        let res = Z3_LazyMbp ctx model x benchmark_formulae
                        let var_value =
                            (model.Consts
                            |> Seq.find (fun (e: KeyValuePair<FuncDecl, Expr>) -> e.Key=x)).Value :?> BitVecNum
                        
                        let x = (x.Name.ToString (), var_value.SortSize) |> ctx.MkBVConst
                        let naive_mbp = List.map (fun (e: BoolExpr) -> e.Substitute ( x , var_value) :?> BoolExpr) benchmark_formulae
                        let in_formula = And benchmark_formulae
                        let ss = List.map (fun x -> x.ToString()) res
                        let ss2 = List.map (fun x -> x.ToString()) benchmark_formulae
                        let is_approximation = is_tautology_z3 (And res =>. exists x in_formula)
                        let is_equiv = is_tautology_z3 (And res <=>. exists  x in_formula)
                        let naive_mbp_is_correct = is_tautology_z3 (And naive_mbp =>. exists x in_formula)
                        let naive_mbp_is_equiv = is_tautology_z3 (And naive_mbp <=>. exists x in_formula)
                        let is_naive = is_tautology_z3 (And res <=>. And naive_mbp)
                        if not is_naive && List.length res > 0 then
                            let k = 1
                            true
                        else
                            false
let findDeepLinearBenchmarks =     
    let files = File.ReadAllLines("/Volumes/MyPassport/bvt/sat_list2.txt")
    let data =
        files
        |> Seq.mapi is_some_lia_conjuncts
        |> Seq.take 1000
        |> Async.Parallel
        |> Async.RunSynchronously
        |> Seq.filter (snd>>((>=) 4))
        |> Seq.map fst
        |> List.ofSeq
    let s = String.Join(",", List.map (fun x -> x.ToString()) data)
    s
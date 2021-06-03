module BVTProver.BenchmarkParser


open System.Collections.Generic
open Microsoft.Z3

open System.Diagnostics
open BVTProver
open Helpers
open System.IO
open Bvt
open Mbp
open Formula
open FormulaActions
open Microsoft.Z3
open Z3Patterns
open Substitution
open RewriteRules.Rule1
open RewriteRules.Rule2
open RewriteRules.Rule3
open RewriteRules.Rule4
open System

let private is_bv_model (model: Model) =
    Seq.forall (fun (e: KeyValuePair<FuncDecl, Expr>) -> e.Value.IsBV) model.Consts      


        
let get_model_z3_many (ctx: Context) (expr: BoolExpr[]) =    
    let solver = ctx.MkSolver()
    solver.Set("timeout", 5000u) // todo make configurable
    solver.Add (expr) 
    if solver.Check()=Status.SATISFIABLE then
        Some solver.Model
    elif solver.Check()=Status.UNKNOWN then
        None
    else
        None

let private deserialize_model (ctx: Context) m =
    let s = ctx.MkSolver()
    s.FromString m
    match s.Check() with
    | Status.SATISFIABLE -> Some s.Model
    | _ -> None

let private get_mid_element values =
    let mid = (Seq.length values) / 2
    values |> Seq.take (Math.Max(mid, 1)) |> Seq.last

(* check that cube is rewritable w.r.t the model & the random var in the model *)
let is_rewritable cube (model: Model) =
    let model = convert_model model
    let x = get_mid_element model.Keys

    let cube =
        cube
        |> List.ofArray
        |> List.map (convert_z3 >> as_formula)
        |> List.collect (TryRewrite x model)

    let residual, open_conjuncts =
        List.partition (formula_contains (Var x)) cube

    match residual with
    | [] -> false
    | Rule1 model x _
    | Rule2 model x _
    | Rule3 model x _
    | Rule4 model x _ -> true
    | _ -> false

type private Result =
    | ExactButTrivial of int64
    | Trivial of int64
    | Interpolation of int64
    | Failed of int64

let private test_mbpZ raw_cube model =
    let watch = Stopwatch.StartNew()
    let model = convert_model model
    let x = get_mid_element model.Keys
    let cube =
        raw_cube
        |> List.ofArray
        |> List.map (convert_z3 >> as_formula)
        |> List.collect (TryRewrite x model)

    let mbp = MbpZ model x cube
    let time = watch.ElapsedMilliseconds

    let is_interpolation =
        is_tautology (And mbp => Exists(Var x, And cube))

    let is_trivial =
        is_tautology (And mbp <=> And(List.map (x --> model) cube))

    let is_correct =
        not (List.exists (formula_contains (Var x)) mbp)

    let is_ok = is_interpolation && is_correct
    if is_ok then
        if is_trivial then
            let is_equiv =
                is_tautology (And mbp <=> Exists(Var x, And cube))

            if is_equiv then ExactButTrivial time else Trivial time
        else
            Interpolation time
    else
        Failed time


let testBenchmarkOnModel file linear model =
    try
        let part_len = Array.length linear

        let avg_depth = ((linear|> Array.map (z3_depth_formula 1)|> Array.sum) / part_len)
        if is_bv_model model && model.Decls.Length > 0 && is_rewritable linear model then
            // model does not have trivial boolean values
            match test_mbpZ linear model with
            | ExactButTrivial _ -> "Exact (Trivial) MBP!"
            | Trivial _ -> "Trivial MBP!"
            | Interpolation time ->
                sprintf
                    "Good Interpolation MBP! | %dms | %d total | %d depth"
                    time
                    part_len
                    avg_depth
            | Failed _ -> "Bad MBP!" + "| Yes " + file
        else
            "No " + file
    with err -> "No (error)"
let profileBenchmark (file: string) =
    let ctx = new Context()
    let expressions = ctx.ParseSMTLIB2File file

    let linear, residual =
        expressions
        |> (Array.partition is_LIA_z3)

    let model = get_model_z3_many ctx linear

    match model with
    | Some model -> testBenchmarkOnModel file linear model
    | None -> sprintf "no model (or timeout)| No %s" file

let findBenchmarksWithSupportedSegments file_of_sats =
    let files = File.ReadAllLines file_of_sats

    let filter =
        Seq.filter (not<<str_contains "Sage2/bench_17801.smt2") // ignore too huge benchmarks
        >> Seq.filter (not<<str_contains "Sage2/bench_10590.smt2")
        >> Seq.filter (not<<str_contains "Sage2/bench_10190.smt2")
        >> Seq.filter (not<<str_contains "Sage2/bench_1008.smt2")
        >> Seq.filter (not<<str_contains "Sage2/bench_10130.smt2")
        >> Seq.filter (not<<str_contains "Sage2/bench_16831.smt2")
        >> Seq.iter (profileBenchmark >> (printfn "%s"))

    filter files

let findLinearBenchmarks file_of_sats =
    let files = File.ReadAllLines file_of_sats

    let is_deep_and_linear =
        Seq.filter is_LIA_z3
        >> Seq.exists (z3_depth_formula 0 >> (<=) 2)

    let ctx = new Context()

    let deep_linear_benchmarks = // (ignore too huge benchmarks)
           Seq.filter (not<<str_contains "2019-Mann/ridecore-qf_bv-bug.smt2")
        >> Seq.filter (not<<str_contains "Sage2/bench_16265.smt2")
        >> Seq.filter (not<<str_contains "Sage2/bench_3774.smt2")
        >> Seq.filter (not<<str_contains "Sage2/bench_5994.smt2")
        >> Seq.filter (ctx.ParseSMTLIB2File >> is_deep_and_linear)

    Seq.iter (printfn "%s") (deep_linear_benchmarks files)

let profileBenchmarks file_with_benchmarks =
    let files = File.ReadAllLines file_with_benchmarks
    Array.iter (profileBenchmark >> (printfn "%s")) files

let project_all_vars file =
    let ctx = new Context()
    let cube = file |> ctx.ParseSMTLIB2File |> List.ofArray
    
    let solver = ctx.MkSolver ()
    solver.Add cube    
    solver.Check ()
    
    for _x in solver.Model.Decls do
        let mbp = Z3_LazyMbp ctx (solver.Model) _x cube
        sprintf "%A\n" mbp
    0
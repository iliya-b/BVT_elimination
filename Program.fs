module BVTProver.Program
open System
open System.Threading
open System.Threading.Tasks
open BVTProver
open BenchmarkParser

open System.IO
open Bvt
open Mbp
open Formula
open FormulaActions
open Microsoft.Z3
open Z3Patterns
open RewriteRules.Rule1
open RewriteRules.Rule2
open RewriteRules.Rule3
open RewriteRules.Rule4
    
    
let deserialize_model (ctx: Context) m =
        let s = ctx.MkSolver ()
        s.FromString m
        match s.Check () with
        | Status.SATISFIABLE -> Some s.Model
        | _ -> None
        
(* check that cube is rewritable w.r.t the model & the last var in the model *)
let is_rewritable cube model =
    if is_bv_model model then  // model does not have trivial boolean values
        let model = convert_model model
        let x = Seq.last model.Keys
        let raw_linear_part, _ = Array.partition is_LIA_z3 cube
        let cube = raw_linear_part
                    |> List.ofArray
                    |> List.map (convert_z3>>as_formula)
                    |> List.collect (TryRewrite x model)
        let residual, open_conjuncts = List.partition (formula_contains (Var x)) cube
        match residual with
        | [] -> false
        | Rule1 model x _ 
        | Rule2 model x _ 
        | Rule3 model x _ 
        | Rule4 model x _ -> true
        | _ -> false
    else
        printfn "not bv model"
        false
let testBenchmarkOnModel (file: string) (ctx: Context) model =
    try
            let expressions = ctx.ParseSMTLIB2File file
            match model with
                | Some model ->
                    if is_rewritable expressions model then
                        printfn "%s" file
                        true
                    else
                        false
                | None -> failwith "unexpected unsat expression"
    with
    | e ->
        printfn "%s" e.Message
        false
        
let testModels () =
    let file_of_sats = "/Users/null_pointer/ttt/z3_models.txt"
    let files = (File.ReadAllText file_of_sats).Split "|||"
    let filter (file: string) =
        let spl = file.Trim().Split ":"
        if spl.Length < 2 then
            false
        else
            let file, serialized_model = spl.[0], spl.[1]
            let ctx = new Context ()
            let model = deserialize_model ctx serialized_model
            testBenchmarkOnModel file ctx model
        
    let rewritable = Seq.filter filter files
    printfn "%d" (Seq.length rewritable)
    0
        
        
let testBenchmarkOnLinearPart (file: string) =
    try
            let file = "/Volumes/MyPassport/bvt/QF_BV/" + file
            let ctx = new Context ()
            let expressions = ctx.ParseSMTLIB2File file
            if Array.length expressions > 1000 then
                printfn "Deep > 1000 %s" file
            else
                ignore 0
            let linear, _ = Array.partition is_LIA_z3 expressions
            let model = get_model_z3_many ctx linear
            match model with
                | Some model ->
                    if is_rewritable linear model then // check just for linear part
                        printfn "Yes %s" file
                        true
                    else
                        printfn "No %s" file
                        false
                | None ->
                    printfn "Timed out %s" file
                    false
    with
    | e ->
        printfn "No (error) %s" e.Message
        false

let findBenchmarksWithSupportedSegments () =
    let file_of_sats = "/Users/null_pointer/RiderProjects/BVTProver/left_deep_benchmarks2.txt"
    let files = File.ReadAllLines file_of_sats
    let filter =
        Seq.filter ((<>) "Sage2/bench_17801.smt2") >>
        Seq.filter ((<>) "Sage2/bench_10590.smt2") >>
        Seq.filter ((<>) "Sage2/bench_10190.smt2") >>
        Seq.filter ((<>) "Sage2/bench_1008.smt2") >>
        Seq.filter ((<>) "Sage2/bench_10130.smt2") >>
        Seq.filter ((<>) "Sage2/bench_16831.smt2") >>
        Seq.filter testBenchmarkOnLinearPart
    let rewritable = filter files
    printfn "%d" (Seq.length rewritable)
    0
let findLinearBenchmarks () =
    let file_of_sats = "/Volumes/MyPassport/bvt/sat_list2.txt"
    let files = File.ReadAllLines file_of_sats
    
    let is_deep_and_linear =
        Seq.filter is_LIA_z3 >> Seq.exists (z3_depth_formula 0 >> (<=) 2)
        
    let ctx = new Context()
        
    let deep_linear_benchmarks =
        Seq.filter ((<>) "/Volumes/MyPassport/bvt/QF_BV/2019-Mann/ridecore-qf_bv-bug.smt2") >>
        Seq.filter ((<>) "/Volumes/MyPassport/bvt/QF_BV/Sage2/bench_16265.smt2") >>
        Seq.filter ((<>) "/Volumes/MyPassport/bvt/QF_BV/Sage2/bench_3774.smt2") >>
        Seq.filter ((<>) "/Volumes/MyPassport/bvt/QF_BV/Sage2/bench_5994.smt2") >>
        Seq.filter (ctx.ParseSMTLIB2File>>is_deep_and_linear)
        
    Seq.iter (printfn "%s") (deep_linear_benchmarks files)
    
    0
    
[<EntryPoint>]
let main argv = findBenchmarksWithSupportedSegments ()
module BVTProver.Program
open System
open System.Collections.Generic
open BVTProver
open BenchmarkParser

open System.IO
open Bvt
open Mbp
open Formula
open FormulaActions
open Microsoft.Z3
open Z3Patterns

let m222ain argv =
    
    let deserialize_model (ctx: Context) m =
        let s = ctx.MkSolver ()
        s.FromString m
        match s.Check () with
        | Status.SATISFIABLE -> Some s.Model
        | _ -> None
    
    let ctx = new Context()
    let deserialize_model = deserialize_model ctx

    let files =
        "/Users/null_pointer/ttt/z3_models.txt"
        |> File.ReadAllText 
        |> (fun x -> x.Split ("|||", StringSplitOptions.RemoveEmptyEntries))
        |> Seq.filter (fun x -> x.Trim().Length > 0)
        |> Seq.map (fun x ->
            let arr = x.Split ":"
            let jj  = ctx.ParseSMTLIB2String arr.[1]
            let m = deserialize_model arr.[1]
            arr.[0], m)
        |> Seq.filter (snd>>Option.isSome)
        |> Seq.filter (snd>>Option.get>>(fun x -> Seq.forall (fun (e: KeyValuePair<'a, Expr>) -> (e.Value :?> BitVecExpr).SortSize <= 32u) x.Consts))
    
    printfn "%A" (Seq.map fst files)
    let get_first collection =
        if Seq.length collection = 0 then
            failwith "empty collection"
        else
            Array.get (collection |> Seq.take 1 |> Seq.toArray) 0
    let doLazyMbp = doLazyMbp ctx
    let expressions = Seq.map (fst>>(fun (s: string) -> s.Trim())>>ctx.ParseSMTLIB2File>>(Array.partition is_LIA_z3)>>fst>>List.ofArray>>(List.map (convert_z3>>as_formula))) files
    
    let models = Seq.map (snd>>Option.get>>convert_model) files
    let TryRewrite rewriter f =
        match rewriter f with
        | None -> [f]
        | Some list -> list
    
    let doMbp formulae (model: IDictionary<VarVector, uint32>) =
        let x = get_first model.Keys
        let cube = List.collect (Rewrite x model |> TryRewrite) formulae
        MbpZ model x cube
    
    let mbp = Seq.map2 doMbp expressions models
    
    let done_ = List.ofSeq mbp
    0
    
[<EntryPoint>]
let main argv =
    let file_of_sats = "/Volumes/MyPassport/bvt/sat_list2.txt"
    let files = File.ReadAllLines file_of_sats
    
    let is_deep_and_linear =
        Seq.filter is_LIA_z3 >> Seq.exists (z3_depth_formula 0 >> (<=) 4)
        
    let ctx = new Context()
    let debug_ f =
        printfn "%s" f
        f
    let deep_linear_benchmarks =
        Seq.filter ((<>) "/Volumes/MyPassport/bvt/QF_BV/2019-Mann/ridecore-qf_bv-bug.smt2") >>
        Seq.filter ((<>) "/Volumes/MyPassport/bvt/QF_BV/Sage2/bench_16265.smt2") >>
        Seq.filter ((<>) "/Volumes/MyPassport/bvt/QF_BV/Sage2/bench_3774.smt2") >>
        Seq.filter ((<>) "/Volumes/MyPassport/bvt/QF_BV/Sage2/bench_5994.smt2") >>
        Seq.filter (ctx.ParseSMTLIB2File>>is_deep_and_linear)
        
    Seq.iter (printfn "%s") (deep_linear_benchmarks files)
    
    0
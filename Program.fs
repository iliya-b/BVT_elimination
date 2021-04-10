module BVTProver.Program
open System
open System.Collections.Generic
open BVTProver
open BenchmarkParser

open MathHelpers
open System.IO
open Bvt
open Mbp
open Formula
open Interpreter
open FormulaActions
open Microsoft.Z3
open FSharp.Collections.ParallelSeq


[<EntryPoint>]
let main argv =
    
    let files = File.ReadAllLines "/Volumes/MyPassport/bvt/sat_deep.txt"
    
    PSeq.choose get_serialized_model files
    |> PSeq.iter (fun (f, m) -> printfn "%s:%s|||\n" f m)

    0
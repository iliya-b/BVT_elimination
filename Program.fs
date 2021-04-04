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
    
    let result =
        PSeq.choose get_serialized_model (Seq.rev files)
    for file, model in result do
        printfn "%s:%s" file model 
    
    0
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
open Microsoft.Z3


[<EntryPoint>]
let main argv =
    
    let files = File.ReadAllLines "/Volumes/MyPassport/bvt/sat_deep.txt"
 
    let kk =
        Seq.exists find_matching_conjuncts (Seq.rev files)
    let total = total_rewritable files
    
    0
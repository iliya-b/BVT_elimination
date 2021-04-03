module BVTProver.Program
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
    
    let total = total_rewritable files
    
    0
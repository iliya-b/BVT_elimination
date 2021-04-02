module BVTProver.Program
open BVTProver
open BenchmarkParser

open MathHelpers
open System.IO

[<EntryPoint>]
let main argv =
    
    let files = File.ReadAllLines "/Volumes/MyPassport/bvt/sat_deep.txt"
    for file in files do
        let res = doLazyMbp file
        ignore res
    0
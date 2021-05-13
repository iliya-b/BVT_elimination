module BVTProver.Program

open BVTProver
open BenchmarkParser



[<EntryPoint>]
let main argv = profileBenchmarks argv.[0]

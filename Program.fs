module BVTProver.Program

open BVTProver
open BenchmarkParser



[<EntryPoint>]
let main argv = test_projection argv.[0] argv.[1]

module BVTProver.Program

open BVTProver
open BenchmarkParser



[<EntryPoint>]
let main argv = elimination argv.[0]

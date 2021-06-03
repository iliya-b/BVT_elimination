module BVTProver.Program

open BVTProver
open BenchmarkParser



[<EntryPoint>]
let main argv = project_all_vars argv.[0]

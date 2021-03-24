module Program

open System
open System.Collections
open Microsoft.Z3

open BVTProver.Helpers

[<EntryPoint>]
let main argv =
    
    let bits = BitArray ([| 43534534 |])
    let integer = integer_of_bits bits
    0
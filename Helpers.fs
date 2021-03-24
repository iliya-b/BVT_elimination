module BVTProver.Helpers

open System
open System.Collections


let reverse_some_tuple t =
    match t with
     | None -> None
     | Some (a, b) -> Some (b, a)
     
let curr_tuple2 F = fun a b -> F (a, b)
let curr_tuple3 F = fun a b c -> F (a, b, c)


let integer_of_bits (x: BitArray) =
    let res = Array.create<byte> 4 0uy
    x.CopyTo(res, 0)       // maximum integer is Int32.MaxValue, not UInt32
    let x = BitConverter.ToUInt32(res, 0) // problem is that BitArray supports converting only to int32
    x
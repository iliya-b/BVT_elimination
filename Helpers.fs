module BVTProver.Helpers

open System
open System.Collections

let unexpected () = failwith "unexpected_value"

let reverse_some_tuple t =
    match t with
     | None -> None
     | Some (a, b) -> Some (b, a)
let str_contains (search: string) (string: string) = string.Contains search

let curr_tuple2 F = fun a b -> F (a, b)
let curr_tuple3 F = fun a b c -> F (a, b, c)

module BVTProver.Helpers


let reverse_some_tuple t =
    match t with
     | None -> None
     | Some (a, b) -> Some (b, a)
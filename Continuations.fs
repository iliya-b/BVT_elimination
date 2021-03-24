module BVTProver.Continuations

let binary_predicate Op fold acc x y =
    let accumulator x = y |> fold (x |> Op >> acc)
    fold accumulator x

let unary_op Op fold acc x = fold (acc << Op) x

type RecursiveTuple<'b, 'a> =
    | Bin of ('a->'a->'a)*'b*'b
    | Unary of ('a->'a)*'b
    | Const of ('a)


let rec fold (map: 'a -> RecursiveTuple<'a, 'b>) (acc: 'b->'b) (x: 'a) : 'b =
        let fold = fold map
        match map x with
             | Bin(op, a, b) -> binary_predicate op fold acc a b
             | Unary(op, a) ->  unary_op op fold acc a
             | Const (op) -> acc op 

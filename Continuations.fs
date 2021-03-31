module BVTProver.Continuations

let private binary_op Op fold acc x y =
    let accumulator x = fold ((Op x) >> acc) y
    fold accumulator x

let private triple_op Op fold acc x y z =
    let accumulator x = fold (fun _x -> (fold (Op x _x) >> acc) z) y
    fold accumulator x

let unary_op Op fold acc x = fold (acc << Op) x

type RecursiveTuple<'b, 'a> =
    | Bin of ('a->'a->'a)*'b*'b
    | Triple of ('a->'a->'a->'a)*'b*'b*'b
    | Unary of ('a->'a)*'b
    | List of ('a list->'a)*('b list)
    | Const of ('a)


let rec fold (map: 'a -> RecursiveTuple<'a, 'b>) (acc: 'b->'b) (x: 'a) : 'b =
        let fold = fold map
        match map x with
             | Bin(op, a, b) -> binary_op op fold acc a b
             | Triple(op, a, b, c) -> triple_op op fold acc a b c
             | Unary(op, a) ->  unary_op op fold acc a
             | Const (op) -> acc op 
             | List (op, lst) -> acc (op (List.map (fold (fun x -> x)) lst ))
             // this case is not tail recursive

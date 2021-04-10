module BVTProver.RewriteRules.Rule4

open BVTProver
open Formula
open FormulaActions
open Interpreter
open MathHelpers


(*
MbpZ(M,φ∧(д<(f(x) div γ)×β)) = MbpZ(M,φ∧(д+1)×γ−1<f(x)×β∧(д<(2n−1) div γ))
*)
type private BoundingInequalityRule4 =
                | Upper_ of Term*uint32*uint32*Term // (f(x) div d)*a < t
                | Lower_ of Term*uint32*uint32*Term

let private (|ConstDivision|_|) x expr =
    match expr with
    | Div (Contains (Var x) t, Int d) -> Some(t, d)
    | _ -> None

let private condition_upper bit_len f a b d =
    let MaxNumber = pown_2 bit_len - 1UL |> uint32
    let Int = Int bit_len
    let One = Int 1u
    
    [ f*(Int a) <== (d + One)*(Int b) - One  ; d <! Div(Int MaxNumber, Int b) ]
let private condition_lower bit_len f b y g =
    let MaxNumber = pown_2 bit_len - 1UL|> uint32
    let Int = Int bit_len
    let One = Int 1u
    [ (g + One)*(Int y) - One <! f*(Int b) ; g <! Div(Int MaxNumber, Int y) ]

let private (|BoundWithDivision|_|) M x bit_len conjunct =
    match conjunct with
        | Le (Mult(Int a, ConstDivision x (f, b)), FreeOf x d)
        | Le (Mult(ConstDivision x (f, b), Int a), FreeOf x d) when M |= And(condition_upper bit_len f a b d)
         -> Some (Upper_(f, b, a, d))
        | Lt (FreeOf x g, Mult(Int b, ConstDivision x (f, y)))
        | Lt(FreeOf x g, Mult(ConstDivision x (f, y), Int b)) when M |= And(condition_lower bit_len f b y g)
         -> Some (Lower_(f, y, b, g))
        | _ -> None

let (|Rule4|_|) M x cube =
    let _, bit_len = x
    match some_matches ((|BoundWithDivision|_|) M x bit_len ) cube with
        | Some ((BoundWithDivision M x bit_len _) as conjunct)  -> Some conjunct
        | _ -> None
let apply_rule4 M x conjunct =
    let _, bit_len = x
    let inequality =
        match conjunct with
         | BoundWithDivision M x bit_len t -> t
         | _ -> failwith "Rule4 requires a*(f(x) div b) <= d"
    let rew =
        match inequality with
            | Upper_(f, b, a, d) -> condition_upper bit_len f b a d
            | Lower_(f, b, a, d) -> condition_lower bit_len f b a d

    rew
        

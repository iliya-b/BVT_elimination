module BVTProver.RewriteRules.Rule3

open BVTProver
open Formula
open FormulaActions
open Interpreter
open MathHelpers


(*
    MbpZ(M,φ∧(f(x) div δ ≤ d)) = MbpZ(M,φ∧(f(x)≤(d+1)×δ−1)∧(d<(2n−1) div δ))
    MbpZ(M,φ∧((f(x)divδ)×α≤d))=MbpZ (M , φ ∧ ( f (x ) × α ≤ (d + 1) × δ − 1) ∧ (d < (2 −1) div δ ))
*)
type private BoundingInequalityRule3 =
    | Upper_ of Term*uint32*Term
    | Lower_ of Term*uint32*Term

let private (|ConstDivision|_|) x expr =
    match expr with
    | Div (Contains (Var x) t, Int d) -> Some(t, d)
    | _ -> None

let private (|BoundWithDivision|_|) M x bit_len conjunct =
    let MaxNumber = pown_2 bit_len - 1UL |> uint32
    let Int = Int bit_len
    match conjunct with
        | Le (ConstDivision x (f, b), FreeOf x d) when M |= (d <! Int (MaxNumber/b)) -> Some (Upper_(f, b, d))
        | Lt (FreeOf x d, ConstDivision x (f, b)) when M |= (d <! Int (MaxNumber/b)) -> Some (Lower_(f, b, d))
        
        | Le (ConstDivision x (f, b), FreeOf x d) 
        | Lt (FreeOf x d, ConstDivision x (f, b)) ->
            let j = 999
            None
        | _ -> None


let (|Rule3|_|) M x cube =
    let _, bit_len = x
    match some_matches ((|BoundWithDivision|_|) M x bit_len) cube with
        | Some ((BoundWithDivision M x bit_len _) as conjunct)  -> Some conjunct
        | _ -> None
let apply_rule3 M x conjunct =
    let _, bit_len = x
    let MaxNumber = pown_2 bit_len - 1UL |> uint32
    let Int = Int bit_len
    let One = Int 1u

    let inequality =
        match conjunct with
        | BoundWithDivision M x bit_len t -> t
        | _ -> failwith "Rule3 requires conjunct of form: t(x) div d <= f ; f > t(x) div d "
    let rew =
        match inequality with
            | Upper_ (f, b, d) -> [ f <== (d + One) * (Int b) - One ; d <== Div(Int MaxNumber, Int b) ]
            | Lower_ (f, y, g) -> [ (g + One) * (Int y) - One <! f ; g <== Div(Int MaxNumber, Int y) ]

    rew
        

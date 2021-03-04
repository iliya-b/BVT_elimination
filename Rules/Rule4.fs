module BVTProver.RewriteRules.Rule4

open BVTProver
open Formula
open FormulaActions


type BoundingInequalityRule4 =
                | Upper_ of Term*int*int*Term // (f(x) div d)*a < t
                | Lower_ of Term*int*int*Term

let (|ConstDivision|_|) x (expr: Term): (Term * int) option =
    match expr with
    | Div (Contains x t, d) -> Some(t, d)
    | _ -> None

let private condition_upper f a (b: int) (d: Term) = [ f*(Int a) <== (d + (Int 1))*(Int b) - (Int 1)  ; d <! Div(Term.Max, b) ]
let private condition_lower f b (y: int) (g: Term) = [ (g + (Int 1))*(Int y) - (Int 1) <! f*(Int b) ; g <! Div(Term.Max, y) ]

let (|BoundWithDivision|_|) (M: Map<string, int>) x (conjunct: Formula) =
    match conjunct with
        | Le (AsMult(Int a, ConstDivision x (f, b)
        | ConstDivision x (f, b), Int a), FreeOf x d) when M |= And(condition_upper f a b d) -> Some (Upper_(f, b, a, d))
        | Lt (FreeOf x g, AsMult(Int b, ConstDivision x (f, y)
        | ConstDivision x (f, y), Int b)) when M |= And(condition_lower f b y g) -> Some (Lower_(f, y, b, g))
        | _ -> None


let (|Rule4|_|) (M: Map<string, int>) x (cube: Cube) =
    match cube.some_matches  ((|BoundWithDivision|_|) M x) with
        | Some ((BoundWithDivision M x inequality) as conjunct)  -> Some (inequality, conjunct)
        | _ -> None
let apply_rule4 M x (cube: Cube) (inequality, conjunct)=
    let rew =
        match inequality with
            | Upper_(f, b, a, d) -> condition_upper f b a d
            | Lower_(f, b, a, d) -> condition_lower f b a d

    (List.except [ conjunct ] cube.conjuncts) @ rew |> Cube
        

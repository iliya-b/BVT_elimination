module BVTProver.RewriteRules.Rule4

open BVTProver
open Formula
open FormulaActions


type private BoundingInequalityRule4 =
                | Upper_ of Term*uint32*uint32*Term // (f(x) div d)*a < t
                | Lower_ of Term*uint32*uint32*Term

let private (|ConstDivision|_|) x expr =
    match expr with
    | Div (Contains x t, Int d) -> Some(t, d)
    | _ -> None

let private condition_upper f a b d = [ f*(Int a) <== (d + Term.One)*(Int b) - Term.One  ; d <! Div(Term.Max, Int b) ]
let private condition_lower f b y g = [ (g + Term.One)*(Int y) - Term.One <! f*(Int b) ; g <! Div(Term.Max, Int y) ]

let private (|BoundWithDivision|_|) M x conjunct =
    match conjunct with
        | Le (AsMult(Int a, ConstDivision x (f, b)
        | ConstDivision x (f, b), Int a), FreeOf x d) when M |= And(condition_upper f a b d) -> Some (Upper_(f, b, a, d))
        | Lt (FreeOf x g, AsMult(Int b, ConstDivision x (f, y)
        | ConstDivision x (f, y), Int b)) when M |= And(condition_lower f b y g) -> Some (Lower_(f, y, b, g))
        | _ -> None

let (|Rule4|_|) M x cube =
    match some_matches ((|BoundWithDivision|_|) M x) cube with
        | Some ((BoundWithDivision M x _) as conjunct)  -> Some conjunct
        | _ -> None
let apply_rule4 M x conjunct =
    let inequality =
        match conjunct with
         | BoundWithDivision M x t -> t
         | _ -> failwith "Rule4 requires a*(f(x) div b) <= d"
    let rew =
        match inequality with
            | Upper_(f, b, a, d) -> condition_upper f b a d
            | Lower_(f, b, a, d) -> condition_lower f b a d

    rew
        

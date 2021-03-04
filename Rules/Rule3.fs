module BVTProver.RewriteRules.Rule3

open BVTProver
open Formula
open FormulaActions


type private BoundingInequalityRule3 =
    | Upper_ of Term*int*Term
    | Lower_ of Term*int*Term

let private (|ConstDivision|_|) x (expr: Term): (Term * int) option =
    match expr with
    | Div (Contains x t, d) -> Some(t, d)
    | _ -> None

let private (|BoundWithDivision|_|) (M: Map<string, int>) x (conjunct: Formula) =
    match conjunct with
        | Le (ConstDivision x (f, b), FreeOf x d) when M |= (d <== Div(Term.Max, b)) -> Some (Upper_(f, b, d))
        | Lt (FreeOf x d, ConstDivision x (f, b)) when M |= (d <! Div(Term.Max, b)) -> Some (Lower_(f, b, d))
        | _ -> None


let (|Rule3|_|) (M: Map<string, int>) x (cube: Formula list) =
    match some_matches ((|BoundWithDivision|_|) M x) cube with
        | Some ((BoundWithDivision M x _) as conjunct)  -> Some conjunct
        | _ -> None
let apply_rule3 M x conjunct =
    let inequality =
        match conjunct with
        | BoundWithDivision M x t -> t
        | _ -> failwith "Rule3 requires conjunct of form: t(x) div d <= f ; f > t(x) div d "
    let rew =
        match inequality with
            | Upper_ (f, b, d) -> [ f <== (d + Term.One) * (Int b) - Term.One ; d <== Div(Term.Max, b) ]
            | Lower_ (f, y, g) -> [ (g + Term.One) * (Int y) - Term.One <! f ; g <== Div(Term.Max, y) ]

    rew
        

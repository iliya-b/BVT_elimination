module BVTProver.Substitution
open System.Collections.Generic
open BVTProver
open Formula
open FormulaActions
open Continuations
open Helpers


let private predicate op a b =
    match a, b with
    | Term a, Term b -> op (a, b) |> Formula
    | _ -> unexpected ()

let private operation op a b =
    match a, b with
    | Term a, Term b -> op (a, b) |> Term
    | _ -> unexpected ()

let private bool op a b =
    match a, b with
    | Formula a, Formula b -> op (a, b) |> Formula
    | _ -> unexpected ()

let private extract x a b =
    match x with
    | Term x -> (x, a, b) |> Extract |> Term
    | _ -> unexpected ()

let private zero_extend x d =
    match x with
    | Term x -> (x, d) |> ZeroEx |> Term
    | _ -> unexpected ()
let private ite a b c =
    match a, b, c with
    | Formula a, Term b, Term c -> (a, b, c) |> Ite |> Term
    | _ -> unexpected ()
let private replace_term (model: IDictionary<VarVector, Term>) x =
    if model.ContainsKey x then
        model.[x]
    else
        Var x
    |> Term
    
let private expr_substitute (model: IDictionary<VarVector, Term>) =
    let replace_term = replace_term model
    formula_mapper
            (predicate Equals)
            (predicate Lt)
            (predicate Le)
            (predicate SLt)
            (predicate SLe)
            (bool (fun (a, b) -> [a; b] |> And))
            (bool (fun (a, b) -> [a; b] |> Or))
            (bool (fun (a, b) -> [a; b] |> Xor))
            (bool Implies)
            (bool Iff)
            (fun _ _ -> unexpected ()) // cannot substitute \exists
            (function Formula f -> f |> Not |> Formula | _ -> unexpected ())
            (Formula True)
            (Formula False)
            (fun x len -> replace_term (x, len))
            (operation Mult)
            (operation Plus)
            (operation BitAnd)
            (operation BitOr)
            (operation BitXor)
            (operation ShiftRightLogical)
            (operation ShiftLeft)
            (fun bits size -> (bits, size) |> Term.Integer |> Term)
            zero_extend
            extract
            ite
            (operation Div)
            (operation SDiv)
            (operation SRem)
            (operation Rem)
            (operation SMod)
            (function Term f -> f |> Inv |> Term | _ -> unexpected ())
            (operation Concat)
            (function Term f -> f |> BitNot |> Term | _ -> unexpected ())

            

let substitute_formula (model: IDictionary<VarVector, Term>) F =
    let res = fold (expr_substitute model) (fun x -> x) (Formula F)
    match res with
    | Formula F -> F
    | _ -> unexpected ()



(* replace only the x variable with corresponding value in the model *)
let inline (-->) (x: VarVector) (model: IDictionary<VarVector, uint32>) =
    let _, bit_len = x
    substitute_formula <| (dict [x, Int bit_len model.[x]])

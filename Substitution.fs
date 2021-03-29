module BVTProver.Substitution

open System.Collections
open System.Collections.Generic
open System.Net.Http
open BVTProver
open Formula
open FormulaActions
open Continuations
open Helpers


let predicate op a b =
    match a, b with
    | Term a, Term b -> op (a, b) |> Formula
    | _ -> unexpected ()

let operation op a b =
    match a, b with
    | Term a, Term b -> op (a, b) |> Term
    | _ -> unexpected ()

let bool op a b =
    match a, b with
    | Formula a, Formula b -> op (a, b) |> Formula
    | _ -> unexpected ()

let extract x a b =
    match x with
    | Term x -> (x, a, b) |> Extract |> Term
    | _ -> unexpected ()

let zero_extend x d =
    match x with
    | Term x -> (x, d) |> ZeroEx |> Term
    | _ -> unexpected ()

let replace_term (model: IDictionary<string, Term>) var_name len =
    if model.ContainsKey var_name then
        model.[var_name]
    else
        Var (var_name, len)
    |> Term
let private expr_substitute (model: IDictionary<string, Term>) =
    let replace_term = replace_term model
    formula_mapper
            (predicate Equals)
            (predicate Lt)
            (predicate Le)
            (predicate SLt)
            (predicate SLe)
            (bool (fun (a, b) -> [a; b] |> And))
            (bool (fun (a, b) -> [a; b] |> Or))
            (bool Implies)
            (bool Iff)
            (fun a b -> unexpected ()) // cannot interpret \exists
            (function Formula f -> f |> Not |> Formula | _ -> unexpected ())
            (Formula True)
            (Formula False)
            replace_term
            (operation Mult)
            (operation Plus)
            (operation BitAnd)
            (operation BitOr)
            (operation ShiftRightLogical)
            (operation ShiftLeft)
            (fun bits size -> (bits, size) |> Term.Integer |> Term)
            zero_extend
            extract
            (fun (Formula condition) (Term _if) (Term _else) -> (condition, _if, _else) |> Ite |> Term)
            (operation Div)
            (function Term f -> f |> Inv |> Term | _ -> unexpected ())
            
            

let substitute_formula model F =
    let res = fold (expr_substitute model) (fun x -> x) (Formula F)
    match res with
    | Formula F -> F
    | _ -> unexpected ()
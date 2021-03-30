module BVTProver.Mbp

open System.Collections.Generic
open Formula
open RewriteRules.Rule1
open RewriteRules.Rule2
open RewriteRules.Rule3
open RewriteRules.Rule4
open FormulaActions
open Substitution
open Bvt

let MbpZ (M: IDictionary<string, uint32>) (x: VarVector) cube =
    let rec Loop acc cube =
        let residual, open_conjuncts = List.partition (formula_contains (Var x)) cube
        let acc = open_conjuncts @ acc
        match residual with
        | [] -> acc
        | Rule1 M x _ -> residual
        | Rule2 M x all_conjuncts ->
            acc @ apply_rule2 M x all_conjuncts
        | Rule3 M x conjunct ->
            Loop ((apply_rule3 M x conjunct) @ acc) (List.except [conjunct] residual)
        | Rule4 M x conjunct ->
            Loop ((apply_rule4 M x conjunct) @ acc) (List.except [conjunct] residual)
        | cube -> acc @ List.map (x --> M) cube
    Loop [] cube

let private TryRewrite rewriter f =
    match rewriter f with
    | [False] -> [f]
    | list -> list

let LazyMbp M x cube =  // bit_len is related to arithmetic part
    let Rewrite = Rewrite x M
    let Normalize = Normalize x M

    let raw_linear_part, bvt_part = List.partition is_LIA_formula cube
    
    let linear_conjuncts = // make literals with x be like f(x) <= a or a<f(x)
        List.collect (TryRewrite Rewrite) >> List.collect Normalize
        <| raw_linear_part
    
    let P = MbpZ M x linear_conjuncts
    
    let implies_cube fs = And fs => Exists (Var x, And cube)
    let project = List.map (x --> M)
    
    let S = project bvt_part
    let S =
        if is_tautology (implies_cube (S @ P)) then
            S
        else
            S @ (project linear_conjuncts)
    

    let remove_unnecessary_projections acc f =
        let S = List.except [f] acc
        if is_tautology (P@S |> implies_cube) then
            S
        else
            acc
            
    P @ List.fold remove_unnecessary_projections S S
        
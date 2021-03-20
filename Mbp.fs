module BVTProver.Mbp

open System.Collections.Generic
open Formula
open Microsoft.Z3
open Microsoft.Z3
open Microsoft.Z3
open RewriteRules.Rule1
open RewriteRules.Rule2
open RewriteRules.Rule3
open RewriteRules.Rule4
open FormulaActions
open Bvt

let var_name x =
        match x with
         | Var name -> name
         | _ -> failwith "x must be a variable"
       
let rec MbpZ (M: IDictionary<string, uint32>) x cube =
    let d = dict []
    let var_name = var_name x
    let x_mapping = [x, (Int (M.[var_name]))] |> dict
    
    let residual, open_conjuncts = List.partition (formula_contains x) cube

    if List.length residual = 0 then
        open_conjuncts
    else
        let rewritten =
            match residual with
            | Rule1 M x _ -> residual
            | Rule2 M x all_conjuncts -> apply_rule2 M x all_conjuncts
            | Rule3 M x conjunct -> (apply_rule3 M x conjunct) @ (MbpZ M x (List.except [conjunct] residual)) 
            | Rule4 M x conjunct -> (apply_rule4 M x conjunct) @ (MbpZ M x (List.except [conjunct] residual))
            | cube -> List.map (substitute_formula x_mapping) cube

        open_conjuncts @ rewritten


let LazyMbp M x cube =
    let var_name = var_name x
    let linear, bitvector = List.partition is_LIA_formula cube
    
    let P = MbpZ M x linear
    let x_mapping = [x, Int (M.[var_name])] |> dict
    let S = List.map (substitute_formula x_mapping) bitvector
    let checker = Not (And (P @ S) => Exists(x, And cube))
    let ctx = new Context()
    let solver = ctx.MkSolver()
    solver.Add(z3fy_formula ctx checker)

    if solver.Check()=Status.SATISFIABLE then
        let mutable S1 = S @ (List.map (substitute_formula x_mapping) linear)
        for s in S do
            let S2 = List.except [s] S
            let checker = And (P @ S2) => Exists(x, And cube)
            let solver = ctx.MkSolver()
            solver.Add(z3fy_formula ctx checker)
            if solver.Check()=Status.UNSATISFIABLE then
                S1 <- S2
            else
                S1 <- S1
        P @ S1
    else
        P @ S
//    if interpret_term
    
//    let residual, open_conjuncts = List.partition (formula_contains x) cube

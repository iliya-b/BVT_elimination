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
open Substitution
open Bvt
let var_name x =
        match x with
         | Var (name, s) -> name
         | _ -> failwith "x must be a variable"

let rec MbpZ (M: IDictionary<string, uint32>) x bit_len cube =
    let MbpZ = MbpZ M x bit_len
    let d = dict []
    let var_name = var_name x
    let Int = Int bit_len
    let x_mapping = [var_name, (Int (M.[var_name]))] |> dict
    
    
    let (|Rule1|_|) = (|Rule1|_|) M var_name bit_len
    let (|Rule2|_|) = (|Rule2|_|) M var_name bit_len
    let (|Rule3|_|) = (|Rule3|_|) M var_name bit_len
    let (|Rule4|_|) = (|Rule4|_|) M var_name bit_len

    let residual, open_conjuncts = List.partition (formula_contains x) cube

    if List.length residual = 0 then
        open_conjuncts
    else
        let rewritten =
            match residual with
            | Rule1 _ -> residual
            | Rule2 all_conjuncts -> apply_rule2 M var_name bit_len all_conjuncts
            | Rule3 conjunct -> (apply_rule3 M var_name bit_len conjunct) @ (MbpZ (List.except [conjunct] residual)) 
            | Rule4 conjunct -> (apply_rule4 M var_name bit_len conjunct) @ (MbpZ (List.except [conjunct] residual))
            | cube -> List.map (substitute_formula x_mapping) cube

        open_conjuncts @ rewritten

let TryRewrite rewriter f =
    match rewriter f with
    | [False] -> [f]
    | list -> list
let LazyMbp M x bit_len cube =  // bit_len is related to arithmetic part
    let Int = Int bit_len
    let var_name = var_name x
    let linear, bitvector = List.partition is_LIA_formula cube
    let normalize =
        List.collect ((Rewrite bit_len x M) |> TryRewrite) >>
        List.collect (Normalize bit_len x M)
    let linear = normalize linear
    
    let P = MbpZ M x bit_len linear
    printfn "%O" P
    let x_mapping = [var_name, Int (M.[var_name])] |> dict
    let S = List.map (substitute_formula x_mapping) bitvector
    let checker = Not (And (P @ S) => Exists(x, And cube))
    let ctx = new Context()
    let solver = ctx.MkSolver()
    let checker_z3 = z3fy_expression ctx (Formula checker)
    solver.Add(checker_z3 :?> BoolExpr)
    let e = checker_z3.ToString()
    if solver.Check()=Status.SATISFIABLE then
        let _S = S @ (List.map (substitute_formula x_mapping) linear)
        let mutable S1 = _S
        for s in _S do
            let S2 = List.except [s] S1
            let checker = Not (And (P @ S2) => Exists(x, And cube))
            let solver = ctx.MkSolver()
            let checker_z3 = z3fy_expression ctx (Formula checker)

            solver.Add(checker_z3 :?> BoolExpr)
            if solver.Check()=Status.UNSATISFIABLE then
                S1 <- S2
            else
                S1 <- S1
        P @ S1
    else
        P @ S
        
module BVTProver.Mbp

open System.Collections.Generic
open Formula
open Microsoft.Z3
open Microsoft.Z3
open RewriteRules.Rule1
open RewriteRules.Rule2
open RewriteRules.Rule3
open RewriteRules.Rule4
open FormulaActions
open Substitution
open Bvt
open Z3Patterns

let MbpZ (M: IDictionary<VarVector, uint32>) (x: VarVector) cube =
    let rec Loop acc cube =
        let residual, open_conjuncts = List.partition (formula_contains (Var x)) cube
        let acc = open_conjuncts @ acc
        match residual with
        | [] -> acc
        | Rule1 M x _ -> acc
        | Rule2 M x all_conjuncts ->
            acc @ apply_rule2 M x all_conjuncts
        | Rule3 M x conjunct ->
            Loop acc (apply_rule3 M x conjunct) @ (List.except [conjunct] residual)
        | Rule4 M x conjunct ->
            Loop acc (apply_rule4 M x conjunct) @ (List.except [conjunct] residual)
        | cube -> acc @ List.map (x --> M) cube
    Loop [] cube


    

let var_vector func_decl (model: Model) =
    let var_value =
            (model.Consts
            |> Seq.find (fun (e: KeyValuePair<FuncDecl, Expr>) -> e.Key=func_decl)).Value :?> BitVecNum
                        
    (func_decl.Name.ToString (), var_value.SortSize), var_value
    
let private convert_const (x: KeyValuePair<FuncDecl, Expr>) =
    match x.Value with
    | :? BitVecNum as num ->
        (x.Key.Name.ToString(), num.SortSize), num.UInt
    | _ ->
        ("___" + x.Key.Name.ToString(), 1u), 0u  // ignore boolean const

let convert_model (z3_model: Model) =
    let raw_model = z3_model.Consts |> List.ofSeq
    raw_model |> List.map convert_const |> dict
    

let Z3_LazyMbp (ctx: Context) (z3_model: Model) (var: FuncDecl) (cube: BoolExpr list) =
        let is_tautology_z3 = is_tautology_z3 ctx

        let x, var_value = var_vector var z3_model            
        let M = convert_model z3_model
        let existential = ctx.MkExists([| x |> ctx.MkBVConst |], ctx.MkAnd cube)
        
        let raw_linear_part, bvt_part = List.partition is_LIA_z3 cube
        
        let linear_conjuncts =
            raw_linear_part
            |> List.map (convert_z3>>as_formula)
            |> List.collect (TryRewrite x M)

                    
        let P =
            MbpZ M x linear_conjuncts
            |> List.map (Formula>>(z3fy_expression ctx))
            |> List.map (fun e -> e :?> BoolExpr)
            
        let implies_existence (fs: BoolExpr list) = ctx.MkImplies (ctx.MkAnd (Array.ofList fs), existential)
        let project = List.map (fun (e: BoolExpr) -> e.Substitute ( x |> ctx.MkBVConst, var_value) :?> BoolExpr)
            
        let bvt_part_projected    = project bvt_part
        let S =
            if is_tautology_z3 (implies_existence (bvt_part_projected@P)) then
                bvt_part_projected
            else
                bvt_part_projected @ (project raw_linear_part)
            

        let remove_unnecessary_projections acc (f: BoolExpr) =
            let S = List.except [f] acc
            if is_tautology_z3 (implies_existence (P@S)) then
               S
            else
                acc

        P @ List.fold remove_unnecessary_projections S S
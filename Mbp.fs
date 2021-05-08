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
            Loop ((apply_rule3 M x conjunct) @ acc) (List.except [conjunct] residual)
        | Rule4 M x conjunct ->
            Loop ((apply_rule4 M x conjunct) @ acc) (List.except [conjunct] residual)
        | cube -> acc @ List.map (x --> M) cube
    Loop [] cube

let private TryRewrite rewriter f =
    match rewriter f with
    | None -> [f]
    | Some list -> list
    

let var_vector func_decl (model: Model) =
    let var_value =
            (model.Consts
            |> Seq.find (fun (e: KeyValuePair<FuncDecl, Expr>) -> e.Key=func_decl)).Value :?> BitVecNum
                        
    (func_decl.Name.ToString (), var_value.SortSize), var_value
let convert_model (z3_model: Model) =
        let raw_model = z3_model.Consts |> List.ofSeq
        raw_model |> List.map (fun x -> (x.Key.Name.ToString(), (x.Value :?> BitVecNum).SortSize), (x.Value :?> BitVecNum).UInt)
         |> dict

let LazyMbp M x cube =  // bit_len is related to arithmetic part
    let Rewrite = TryRewrite (Rewrite x M)

    let raw_linear_part, bvt_part = List.partition is_LIA_formula cube
    
    if List.length raw_linear_part < 0 then
        []
    else
        let linear_conjuncts = // make literals with x be like f(x) <= a or a<f(x)
            List.collect Rewrite raw_linear_part
        
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
        

let Z3_LazyMbp (ctx: Context) (z3_model: Model) (var: FuncDecl) (cube: BoolExpr list) =  // bit_len is related to arithmetic part

    let x, var_value = var_vector var z3_model
  
    if snd x = 1u then
        []
    else
        let is_tautology_z3 = is_tautology_z3 ctx
            
        let M = convert_model z3_model
        let Rewrite = TryRewrite (Rewrite x M)

        let existential = ctx.MkExists([| x |> ctx.MkBVConst |], ctx.MkAnd cube)

        
        let raw_linear_part, bvt_part = List.partition is_LIA_z3 cube
        
        let linear_conjuncts =
            raw_linear_part
            |> List.map (convert_z3>>as_formula)
            |> List.collect Rewrite

                    
        let P =
            MbpZ M x linear_conjuncts
            |> List.map (Formula>>(z3fy_expression ctx))
            |> List.map (fun e -> e :?> BoolExpr)
            
        let implies_cube (fs: BoolExpr list) = ctx.MkImplies (fs |> List.map (fun (f) -> f :?> BoolExpr) |> Array.ofList |> ctx.MkAnd, existential)
        let project = List.map (fun (e: BoolExpr) -> e.Substitute ( x |> ctx.MkBVConst, var_value) :?> BoolExpr)
            
        let S = project bvt_part
        let S =
            if is_tautology_z3 (implies_cube (S@P)) then
                S
            else
                S @ (project raw_linear_part)
            

        let remove_unnecessary_projections acc (f: BoolExpr) =
                let S = List.except [f] acc
                if is_tautology_z3 (implies_cube (P@S)) then
                    S
                else
                    acc
                    
        P @ List.fold remove_unnecessary_projections S S
                
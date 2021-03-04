module BVTProver.Mbp

open Formula
open RewriteRules.Rule1
open RewriteRules.Rule2
open RewriteRules.Rule3
open RewriteRules.Rule4
open FormulaActions


let rec MbpZ (M: Map<string, int>) (x: Term) (cube: Cube) =
    let var_name =
        match x with
         | Var name -> name
         | _ -> failwith "x must be a variable"
         
    let x_mapping = [x, Int (Map.find var_name M)] |> Map.ofList
    
    let open_conjuncts, residual = cube.split x

    if residual.conjuncts.Length = 0 then
        open_conjuncts
    else
        let residual =
            match residual with
            | Rule1 M x _ -> residual
            | Rule2 M x (lcm, bounds) -> apply_rule2 M x residual (lcm, bounds)
            | Rule3 M x (T, conjunct) -> (apply_rule3 M x residual (T, conjunct)) + (MbpZ M x (residual.remove conjunct)) 
            | Rule4 M x (T, conjunct) -> (apply_rule4 M x residual (T, conjunct)) + (MbpZ M x (residual.remove conjunct))
            | cube -> Cube (List.map (substitute_formula x_mapping) cube.conjuncts)

        open_conjuncts + residual


//let LazyMbp (f: Expr) var (M: Map<Expr, Expr>) =

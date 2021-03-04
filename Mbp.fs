module BVTProver.Mbp

open Formula
open RewriteRules.Rule1
open RewriteRules.Rule2
open RewriteRules.Rule3
open RewriteRules.Rule4
open FormulaActions


let rec MbpZ (M: Map<string, int>) (x: Term) (cube: Formula list) =
    let var_name =
        match x with
         | Var name -> name
         | _ -> failwith "x must be a variable"
         
    let x_mapping = [x, Int (Map.find var_name M)] |> Map.ofList
    
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


//let LazyMbp (f: Expr) var (M: Map<Expr, Expr>) =

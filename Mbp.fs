module BVTProver.Mbp
open Formula
open RewriteRules.Rule1
open RewriteRules.Rule2
open RewriteRules.Rule3
open RewriteRules.Rule4


let rec MbpZ (M: Map<string, int>) (x: Term) (cube: Cube) =
        let mapping = M |> Map.toList |> (List.map (fun (k, e) -> Var k, Int e)) |> Map.ofList
        let x_mapping = Map.filter (fun k _ -> k=x) mapping
        let (open_conjuncts, residual) = cube.split x
        
        if residual.conjuncts.Length=0 then
            open_conjuncts
        else
            let residual: Cube =
                match residual with
                    | Rule1 M x _ -> residual
                    | Rule2 M x (lcm, bounds) -> apply_rule2 M x residual (lcm, bounds)
                    | Rule3 M x (T, conjunct) -> apply_rule3 M x residual (T, conjunct)
                    | cube -> Cube( Array.map (fun (e: Formula) -> e.substitute x_mapping) cube.conjuncts )
            open_conjuncts + residual


//let LazyMbp (f: Expr) var (M: Map<Expr, Expr>) =

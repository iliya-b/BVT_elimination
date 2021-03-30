module BVTProver.RewriteRules.Rule1
open BVTProver
open Formula
open FormulaActions

let private is_tautological x conjunct =    
    match conjunct with
        | Le(Mult(_, ThisVar x), _)  // A*x <= t
        | Le(Mult(ThisVar x, _), _)
        | Le(ThisVar x, _) -> true
        | _ -> false
                           
let (|Rule1|_|) _ x cube =
    if List.forall (is_tautological x) cube then
        Some cube
    else
        None
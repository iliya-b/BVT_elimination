module BVTProver.RewriteRules.Rule1
open BVTProver
open Formula
open FormulaActions

let private is_tautological x conjunct =    
    match conjunct with
        | AsLe(AsMult(t1, ThisVar x | ThisVar x, t1), t2) -> true
        | _ -> false
                           
let (|Rule1|_|) M x cube =
    if List.forall (is_tautological x) cube then
        Some(cube)
    else
        None
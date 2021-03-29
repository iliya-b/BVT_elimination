module BVTProver.RewriteRules.Rule1
open BVTProver
open Formula
open FormulaActions

let private is_tautological x conjunct =    
    match conjunct with
        | AsLe(Mult(_, ThisVar x), _)  // A*x <= t
        | AsLe(Mult(ThisVar x, _), _)
        | AsLe(ThisVar x, _) -> true
        | _ -> false
                           
let (|Rule1|_|) M x bit_len cube =
    let x = Var (x, bit_len)
    if List.forall (is_tautological x) cube then
        Some cube
    else
        None
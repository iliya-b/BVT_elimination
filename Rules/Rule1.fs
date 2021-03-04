module BVTProver.RewriteRules.Rule1
open BVTProver
open Formula
open FormulaActions

let (|TautologicalInequality|_|) x (conjunct: Formula) =    
    match conjunct with
        | AsLe(AsMult(t1, ThisVar x | ThisVar x, t1), t2) -> Some(t1, t2)
        | _ -> None
                           
let (|Rule1|_|) M x (cube: Cube) =
    if cube.each_matches ((|TautologicalInequality|_|) x) then
        Some(cube)
    else
        None
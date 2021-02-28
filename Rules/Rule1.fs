module BVTProver.RewriteRules.Rule1
open BVTProver
open Formula
open MathHelpers
let (|TautologicalInequality|_|) x (conjunct: Formula) =
    let (|ThisVar|_|) = (|ThisVar|_|) x
    
    match conjunct with
        | AsLe(AsMult(t1, ThisVar | ThisVar, t1), t2) -> Some(t1, t2)
        | _ -> None
                           
let (|Rule1|_|) M x (cube: Cube) =
    let (|TautologicalInequality|_|) = (|TautologicalInequality|_|) x
    if cube.each_matches (|TautologicalInequality|_|) then
        Some(cube)
    else
        None
module BVTProver.RewriteRules
open BVTProver
open Formula
open MathHelpers


type BoundingInequality =
    | Upper of int*Term
    | Lower of int*Term
    static member tuplify = function Upper (a, b) | Lower (a, b) -> (a, b)
    static member is_upper = function Upper _ -> true | _ -> false
       
type RuleType = All | Any
let (|Bounds|_|) x (conjunct: Formula) = // such that num*x <= term
    let (|Open|_|) = (|FreeOf|_|) x
    let (|ThisVar|_|) = (|ThisVar|_|) x
    
    match conjunct with
        | AsLe (AsMult (ThisVar, Int d | Int d, ThisVar), Open t) -> Some (Upper(d, t))
        | AsLt (Open t, AsMult (ThisVar, Int d | Int d, ThisVar)) -> Some (Lower(d, t))
        | _ -> None



let (|Rule2|_|) (M: Map<string, int>) x (cube: Cube) =
    let (|Bounds|_|) = (|Bounds|_|) x
    
    // todo: lazy computation
    if cube.each_matches (|Bounds|_|) then
        let bounds = Array.choose (|Bounds|_|) cube.conjuncts
        let tuples = Array.map BoundingInequality.tuplify bounds
        let LCM = tuples |> (Array.map fst)
                  |> Array.toList
                  |> lcmlist
        let side_condition n t = t <== Int((n-1)/(LCM/n))
    
        let var_value = M.Item(match x with | Var s -> s)
        // side conditions
        let lcm_overflows = LCM >= n
        let lcm_multiplied_overflows = var_value * LCM >= n
        let model_satisfies = Array.forall (fun (n, t) -> M |= (side_condition n t) ) tuples 

        if not lcm_overflows
           && not lcm_multiplied_overflows
           && model_satisfies then
            Some(LCM, bounds)
        else
            None
    else
        None

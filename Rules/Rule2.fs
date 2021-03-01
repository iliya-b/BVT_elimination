module BVTProver.RewriteRules.Rule2
open BVTProver
open Formula
open MathHelpers


type BoundingInequality =
    | Upper of int*Term
    | Lower of int*Term
    static member tuplify = function Upper (a, b) | Lower (a, b) -> (a, b)
    static member is_upper = function Upper _ -> true | _ -> false
       
type RuleType = All | Any
let (|Bounds|_|) x (conjunct: Formula) = 
    
    match conjunct with
        | AsLe (AsMult (ThisVar x, Int d | Int d, ThisVar x), FreeOf x t) -> Some (Upper(d, t)) // β×x ≤ b
        | AsLt (FreeOf x t, AsMult (ThisVar x, Int d | Int d, ThisVar x)) -> Some (Lower(d, t)) // a < α×x
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
        let side_condition num t = t <== Int((n-1)/(LCM/num))
    
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

let apply_rule2 M x (cube: Cube) (lcm, bounds) =
    let upper_bounds, lower_bounds = Array.partition BoundingInequality.is_upper bounds
    let interpreted = function | Upper (num, t) | Lower (num, t) -> (t.interpret M) * (lcm / num)
 
    
    let sup = upper_bounds |> Array.minBy interpreted |> BoundingInequality.tuplify
    let inf = lower_bounds |> Array.maxBy interpreted |> BoundingInequality.tuplify
    

    let coefficient_L = fst inf
    let coefficient_U = fst sup
    let term_L = snd inf
    let term_U = snd sup
    
    let side_constraint c t = t <== (Int((n - 1) / (lcm / c)))
    let mk_constraints_on_bounds = function | Lower (num, t) | Upper (num, t) -> side_constraint num t
    
    let make_conjunct2 conjunct =
        match conjunct with
            | Upper (num, t) when num <> coefficient_U && t <> term_U ->
                        Some((t* (Int(lcm / num)) <== term_L * (Int(lcm / coefficient_L))))
            | Lower (num, t) when num <> coefficient_L && t <> term_L ->
                        Some((term_U * (Int(lcm / coefficient_U)) <== t * (Int(lcm / num))))
            | _ -> None

    let c1 = lower_bounds |> Array.map mk_constraints_on_bounds
    let c2 = upper_bounds |> Array.map mk_constraints_on_bounds

    let c3 = cube.conjuncts
                |> (Array.choose ((|Bounds|_|) x))
                |> (Array.choose make_conjunct2)

    let c4 = [| Div(term_L * (Int(lcm / coefficient_L)), lcm) <! Div(term_L * (Int(lcm / coefficient_L)), lcm) |]
    [ c1; c2; c3; c4 ] |> Array.concat |> Cube
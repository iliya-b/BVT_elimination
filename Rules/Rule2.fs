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
    let a, b = Array.partition BoundingInequality.is_upper bounds

    let u_coeffs, upper_bounds =
                    a
                    |> (Array.map BoundingInequality.tuplify)
                    |> Array.unzip

    let l_coeffs, lower_bounds =
                    b
                    |> (Array.map BoundingInequality.tuplify)
                    |> Array.unzip

    let (|Bounds|_|) = (|Bounds|_|) x

    let exact_bound a b =
                    (a, b)
                    ||> Array.map2 (fun n (t: Term) -> (t.interpret M) * (lcm / n))
                    |> Array.indexed
                    |> Array.maxBy snd
                    |> fst

    let U = exact_bound u_coeffs upper_bounds
    let L = exact_bound l_coeffs lower_bounds
    let coefficient_L = Array.get l_coeffs L
    let coefficient_U = Array.get u_coeffs U
    let term_L = Array.get lower_bounds L
    let term_U = Array.get upper_bounds U
    let LCM = lcm

    let constraints_on_bounds = Array.map2 (fun c t -> t <== (Int((n - 1) / (LCM / c))))
    let make_conjunct2 conjunct =
        match conjunct with
            | Upper (num, t) when num <> coefficient_U && t <> term_U ->
                        Some((t* (Int(LCM / num)) <== term_L * (Int(LCM / coefficient_L))))
            | Lower (num, t) when num <> coefficient_L && t <> term_L ->
                        Some((term_U * (Int(LCM / coefficient_U)) <== t * (Int(LCM / num))))
            | _ -> None

    let c1 = (l_coeffs, lower_bounds) ||> constraints_on_bounds

    let c2 = (u_coeffs, upper_bounds) ||> constraints_on_bounds

    let c3 = cube.conjuncts
                |> (Array.choose (|Bounds|_|))
                |> (Array.choose make_conjunct2)

    let c4 = [| Div(term_L * (Int(LCM / coefficient_L)), LCM) <! Div(term_L * (Int(LCM / coefficient_L)), LCM) |]
    [ c1; c2; c3; c4 ] |> Array.concat |> Cube    
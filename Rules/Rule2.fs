module BVTProver.RewriteRules.Rule2
open System.Collections.Generic
open BVTProver
open Formula
open MathHelpers
open FormulaActions
open Interpreter


(*
MbpZ (M,ψ ∧ {a_i<α_i×x} ∧ {β_j×x≤b_j}) =
 ψ ∧ (aL ×(LCM div α_L) div LCM)<(b_U ×(LCM div β_U) ∧ ...
*)

type private BoundingInequality =
    | Upper of uint32*Term // β×x ≤ b
    | Lower of uint32*Term // a < α×x
    static member tuplify = function Upper (a, b) | Lower (a, b) -> (a, b)
    static member is_upper = function Upper _ -> true | _ -> false
       
type RuleType = All | Any
let private (|Bounds|_|) x conjunct = 
    
    match conjunct with
        | Le ( Mult(ThisVar x, Int d), FreeOf x t)
        | Le ( Mult(Int d, ThisVar x), FreeOf x t)        
         -> Some (Upper(d, t)) // β×x ≤ b
        | Le (ThisVar x, FreeOf x t) -> Some (Upper(1u, t)) // x ≤ b
        
        | Lt (FreeOf x t, Mult (Int d, ThisVar x))
        | Lt (FreeOf x t, Mult (ThisVar x, Int d))
         -> Some (Lower(d, t)) // a < α×x
         
        | Lt (FreeOf x t, ThisVar x) -> Some (Lower(1u, t)) // a < x
         
        | _ -> None

let (|Rule2|_|) (M: IDictionary<(string * uint32),uint32>) x cube =
    let var_name, bit_len = x
    let MaxNumber = pown_2 bit_len - 1UL |> uint32
    let Int = Int bit_len

    let (|Bounds|_|) = (|Bounds|_|) x
    
    
    // todo: lazy computation
    if each_matches (|Bounds|_|) cube then
        let bounds = cube |>
                     (List.choose (|Bounds|_|)) |>
                     (List.map BoundingInequality.tuplify)
                     
        let LCM = bounds |> (List.map fst) |> lcmlist
        let side_condition num t = t <== Int (MaxNumber/(LCM/num))
    
        let var_value = M.[x]
        // side conditions
        let lcm_overflows = LCM > MaxNumber
        
        let lcm_multiplied_overflows = var_value * LCM > MaxNumber
        let model_satisfies = List.forall (fun (n, t) -> M |= (side_condition n t) ) bounds 

        if not lcm_overflows
           && not lcm_multiplied_overflows
           && model_satisfies then
            Some(cube)
        else
            None
    else
        None

let apply_rule2 M x cube =
    let _, bit_len = x
    let MaxNumber = pown_2 bit_len - 1UL |> uint32
    let Int = Int bit_len
    
    let bounds = cube |> (List.choose ((|Bounds|_|) x))
    let lcm = bounds |> (List.map (BoundingInequality.tuplify >> fst)) |> lcmlist

    let upper_bounds, lower_bounds = List.partition BoundingInequality.is_upper bounds
    let interpreted = function | Upper (num, t) | Lower (num, t) -> (interpret_term M t |> fst) * (lcm / num)
 
    
    let sup =
        match upper_bounds with
        | [] -> MaxNumber, Var x 
        | list -> list |> List.minBy interpreted |> BoundingInequality.tuplify
        
    let inf =
        match lower_bounds with
        | [] -> 0u, Var x
        | list -> list |> List.maxBy interpreted |> BoundingInequality.tuplify
    
    let coefficient_L, term_L = inf
    let coefficient_U, term_U = sup
    
    let side_constraint c t =
        let bound = MaxNumber / (lcm / c)
        if bound < MaxNumber then
            Some (t <== Int bound)
        else  // trivially true
            None
    let mk_constraints_on_bounds = function | Lower (num, t) | Upper (num, t) -> side_constraint num t
    
    let make_conjunct2 conjunct =
        match conjunct with
            | Upper (num, t) when num <> coefficient_U && t <> term_U ->
                        Some((t* (Int(lcm / num)) <== term_L * (Int(lcm / coefficient_L))))
            | Lower (num, t) when num <> coefficient_L && t <> term_L ->
                        Some((term_U * (Int(lcm / coefficient_U)) <== t * (Int(lcm / num))))
            | _ -> None

    let c1 = lower_bounds |> List.choose mk_constraints_on_bounds
    let c2 = upper_bounds |> List.choose mk_constraints_on_bounds

    let c3 = cube
                |> (List.choose ((|Bounds|_|) x))
                |> (List.choose make_conjunct2)
        
    let c4 = SmartDiv (term_L * (Int (lcm / coefficient_L)), Int lcm) <! SmartDiv (term_U * (Int(lcm / coefficient_U)), Int lcm)
    c4 :: (c1 @ c2 @ c3)
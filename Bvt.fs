module BVTProver.Bvt

open Formula
open FormulaActions
open Interpreter
open MathHelpers
let private getRules conclusion x =
        let _, bit_len = x
        let Int = Int bit_len
        let _0 = Int 0u
        let _1 = Int 1u
        let MaxNumber = pown_2 bit_len - 1u

        let var = Var x
        let contains_var = term_contains var
        let first_term_bounded t y z = contains_var t && not (contains_var y) && not (contains_var z)
        let first_two_terms_bounded t1 t2 y = contains_var t1 && contains_var t2 && not (contains_var y)
        // t(x) - a terms containing x, y/z - x-free terms, a/b - any term
        match conclusion with
            | Le(Plus(t, y), z)
            | Le(Plus(y, t), z) when first_term_bounded t y z -> [
                    [t <== z-y; y <== z] // add1
                    [t <== z-y; _0-y <== t] // add2 
                    [_0-y <== t; y <== z; -(y === _0)] // add3
             ]
            | Le(z, Plus(t, y))
            | Le(z, Plus(y, t)) when first_term_bounded t y z -> [
                [t >== z-y; z <== y-_1]; // add4
                [t >== z-y; t <== _0-y-_1; -(y === _0)] // add5 
                [y === _0; z <== t] // add6
                [-(y === _0); z <== y-_1; var <== _0-y-_1] // add7
              ]
            | Le(Plus(t1, y), t2) when first_two_terms_bounded t1 t2 y -> [
                [ y <== t2 - t1; t1 <== t2; ]; // bothx1
                [ y <== t2 - t1; Inv(t1) <== y; ];  // bothx2
                [ Inv(t1) <==  y; t1 <== t2; -(t1 === _0)] // bothx3
              ]
            | Equals(a, b) -> [ [a <== b; b <== a] ] // eq
            | Not(Equals(a, b)) -> [ [a <! b];  [a >! b]  ] // neq
            | Not(Le(a, b)) -> [ [b <== a-_1; _1 <== a] ] // nule
            
            | Le(Inv(t), y) when first_two_terms_bounded t t y ->
                [ [_0-y <== t] ] // inv
                
            | Le(y, Inv(t)) when first_two_terms_bounded t t y ->
                [ [t <== _0-y] ] // inv
            | Le(Mult(Int k1, ThisVar x), Mult(Int k2, ThisVar x)) ->
                [ [var <== Int ((MaxNumber+1u) * k1 / k2) ] ] // bothx4
            | _ -> []
     
     

let Normalize x M literal =
    // make literal of form: a < f(x) or f(x) <= a
    let _, bit_len = x
    let Int = Int bit_len

    match literal with
    | Le(FreeOf x a, f) ->
        if M |= (a === Int 0u) then
            [ a === Int 0u ]
        else
            [ (a - Int 1u) <! f ]
    | Lt(f, FreeOf x b) ->
        [ Not (b === Int 0u) ; f <== b - Int 1u ]
    | t -> [t]

let rec Rewrite var model formula = // normalization procedure
    
    let where_premises_hold premises =
        let f = List.collect (Rewrite var model) premises
        if model |= And f then                                      
            Some f
        else
            None
                 
    // todo: assert model |= formula
    match formula with
    | cube when not (formula_contains (Var var) cube) -> [cube]
    | Lt(_, Mult(Int _, ThisVar var))
    | Lt(_, ThisVar var)
    | Le(Mult(Int _, ThisVar var), _)
    | Le(ThisVar var, _) -> [formula]
    | cube ->
        let applicable_rules = getRules cube var
        let p = List.tryPick where_premises_hold applicable_rules
        match p with
        | Some conjuncts -> conjuncts
        | None -> [False]
                                      
                                          
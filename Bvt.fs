module BVTProver.Bvt
open Microsoft.Z3
open Z3Patterns

open Formula
open FormulaActions
open Interpreter
open MathHelpers
let private getRules conclusion x =
        let _, bit_len = x
        let Int = Int bit_len
        let _0 = Int 0u
        let _1 = Int 1u

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
                let modulo = pown_2 bit_len
                [ [var <== Int (modulo * (uint64 k1) / (uint64 k2) % modulo |> uint32) ] ] // bothx4
                
            | Le(FreeOf x a, f) -> // xside1 // guarantee to have: a < f(x) or f(x) <= a
                      [ [ a === Int 0u ] ; [ (a - Int 1u) <! f ] ]
            | Lt(f, FreeOf x b) -> // xside2
                [ [ Not (b === Int 0u) ; f <== b - Int 1u ] ]
            | _ -> []
     
(* Normalization. Rewriting tree < 7 *)
let rec private Rewrite_i i var model formula =
    let where_premises_hold premises =
        let rewritten_premises = Seq.map (Rewrite_i (i+1) var model) premises
        let succeeded = Seq.forall Option.isSome rewritten_premises

        if succeeded then
            let f = rewritten_premises
                    |> Seq.map Option.get
                    |> Seq.concat
                    |> List.ofSeq
            if model |= And f then
                Some f
            else
                None
        else
            None
    
//    printfn "%s" (String.replicate i "-")
    // todo: assert model |= formula
    if i >= 7 then // block normalization tree of height >= 7
        None
    else
        match formula with
        | formula when not (formula_contains (Var var) formula) -> Some [formula]
        | Lt(_, Mult(Int _, ThisVar var))
        | Lt(_, ThisVar var)
        | Le(Mult(Int _, ThisVar var), _)
        | Le(ThisVar var, _) -> Some [formula]
        | f -> List.tryPick where_premises_hold (getRules f var)
let Rewrite: string * uint32 -> System.Collections.Generic.IDictionary<(string * uint32),uint32> -> Formula -> Formula list option =
    Rewrite_i 1

(* Rewrite or keep unchanged *)
let TryRewrite var model f =
        match Rewrite var model f with
        | None -> [f]
        | Some cube -> cube
module BVTProver.Bvt

open Formula
open FormulaActions
        
let private getRules conclusion (var: Term) =

        let _0 = Term.Zero
        let _1 = Term.One
        let contains_var = term_contains var
        let var_check (t: Term) (y: Term) (z: Term) = contains_var t && not (contains_var y) && not (contains_var z)
        let var_check2 (t1: Term) (t2: Term) (y: Term)  = contains_var t1 && contains_var t2 && not (contains_var y)
        // t(x) - a terms containing x, y/z - x-free terms, a/b - any term
        match conclusion with
            | Le(Plus(t, y), z)
            | Le(Plus(y, t), z)
            | Ge(z, Plus(t, y))
            | Ge(z, Plus(y, t)) when var_check t y z -> [
                    [t <== z-y; y <== z] // add1
                    [t <== z-y; _0-y <== t] // add2 
                    [_0-y <== t; y <== z; -(y === _0)] // add3
             ]
            | Ge(Plus(t, y), z)
            | Ge(Plus(y, t), z)
            | Le(z, Plus(t, y))
            | Le(z, Plus(y, t)) when var_check t y z -> [
                [t >== z-y; z <== y-_1]; // add4
                [t >== z-y; t <== _0-y-_1; -(y === _0)] // add5 
                [y === _0; z <== t] // add6
                [-(y === _0); z <== y-_1; var <== _0-y-_1] // add7
              ]
            | Le(Plus(t1, y), t2)
            | Le(Plus(y, t1), t2)
            | Ge(t2, Plus(t1, y))
            | Ge(t2, Plus(y, t1)) when var_check2 t1 t2 y -> [
                [ y <== t2 - t1; t1 <== t2; ]; // bothx1
                [ y <== t2 - t1; Inv(t1) <== y; ];  // bothx2
                [ Inv(t1) <==  y; t1 <== t2; -(t1 === _0)] // bothx3
              ]
            | Equals(a, b) -> [ [a <== b; b <== a] ] // eq
            | Not(Equals(a, b)) -> [ [a <! b];  [a >! b]  ] // neq
            | Not(Le(a, b)) -> [ [b <== a-_1; _1 <== a] ] // nule
            | Le(Inv(t), y)
            | Ge(y, Inv(t)) when var_check2 t t y ->
                [ [_0-y <== t] ] // inv
            | Le(y, Inv(t))
            | Ge(Inv(t), y) when var_check2 t t y ->
                [ [t <== _0-y] ] // inv
            | Le(Mult(Int k1, ThisVar var), Mult(Int k2, ThisVar var)) ->
                [ [var <== Int ((Term.MaxNumber+1) * k1 / k2) ] ] // bothx4
            | _ -> []
     

let rec Rewrite (cube: Formula) (var: Term) model i: Formula list = // normalization procedure
               
        let premises_hold premises =
          let f = List.collect (fun p -> Rewrite p var model (i+1)) premises
          if model |= And(Array.ofList f) then                                      
              Some f
          else
              None
 
                    
        // todo: assert cube is cube
        // todo: assert model |= cube
        match cube with
            | cube when not (formula_contains var cube) -> [cube]
            | Le(_, Mult(Int _, ThisVar var))
            | Ge(Mult(Int _, ThisVar var), _)
            | Le(_, ThisVar var)
            | Ge(ThisVar var, _)
            | Le(Mult(Int _, ThisVar var), _)
            | Ge(_, Mult(Int _, ThisVar var)) 
            | Le(ThisVar var, _)
            | Ge(_, ThisVar var) -> [cube]
            | cube -> let applicable_rules = getRules cube var
                      let p = List.tryPick premises_hold applicable_rules
                      match p with
                       | Some conjuncts -> conjuncts
                       | None -> [False]
                                      
                                          
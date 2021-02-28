module BVTProver.Bvt
open System
open Microsoft.Z3
open Microsoft.Z3
open Formula

type BVT(ctx: Context, n: uint32, nn: int) =
        
    member this.ZERO =
        ctx.MkBV(0, n)
    member this.CHECK_MODEL (M: Map<Expr, Expr>) (F: BoolExpr) =
            let s = (M |> Map.toArray |> Array.unzip |> F.Substitute ).Simplify()
            s.IsTrue

    member this.getRules conclusion (var: Term) =

        let _0 = Int 0
        let _1 = Int 1

        let var_check (t: Term) (y: Term) (z: Term) = t.contains var && not (y.contains var) && not (z.contains var)
        let var_check2 (t1: Term) (t2: Term) (y: Term)  = t1.contains var && t2.contains var && not (y.contains var)
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
            | Le(Mult(Int k1, ((Var _) as x)), Mult(Int k2, ((Var _) as _x))) when x=var && _x=var
             -> [ [var <== Int ((pown 2 nn) * k1 / k2) ] ] // bothx4
            | _ -> []
     

    member this.Rewrite (cube: Formula) (var: Term) model i: Formula = // normalization procedure
        
        let (|ThisVar|_|) (term: Term) = if term=var then Some() else None
        
        let premises_hold (result: Formula list option) p =
            if result.IsNone then
                None
            else
                (*printfn "%s %O" (String('_', i)) p*)

                let e = this.Rewrite p var model (i+1)
                let conjuncts = match e with
                                   | And args -> Array.toList args
                                   | t -> [t]
                                                
                match result with
                    | Some literals when model |= e -> Some (conjuncts @ literals)
                    | _ -> (* printfn "%s failed %O" (String('_', i))  (And (conjuncts @ result.Value |> List.toArray)) *)
                           None
                    
        // todo: assert cube is cube
        // todo: assert model |= cube
        match cube with
            | cube when not (cube.contains var) -> cube
            | (Le(_, Mult(Int _, ThisVar)) | Ge(Mult(Int _, ThisVar), _)) -> cube
            | (Le(_, ThisVar) | Ge(ThisVar, _))-> cube
            | (Le(Mult(Int _, ThisVar), _) | Ge(_, Mult(Int _, ThisVar))) -> cube
            | (Le(ThisVar, _) | Ge(_, ThisVar)) -> cube
            | cube -> let list = this.getRules cube var
                      if List.length list = 0 then
                          False
                      else
                          let p = List.tryPick (List.fold premises_hold (Some []))  list
                          match p with
                                | Some conjuncts -> And (List.toArray conjuncts)
                                | None -> False
                                      
                                          
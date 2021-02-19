module BVTProver.Bvt
open Microsoft.Z3
open BVTProver.BvtPatterns
open Microsoft.Z3


type BVT(ctx: Context, n: uint32, nn: int) =
        
    member this.ZERO =
        ctx.MkBV(0, n)
    member this.CHECK_MODEL (M: Map<Expr, Expr>) (F: BoolExpr) =
            let s = F.Substitute( (M |> Map.toArray |> Array.map fst), ( M |> Map.toArray |> Array.map snd ) ).Simplify()
            s.IsTrue
    
    member this.(~-) (t: BoolExpr) = ctx.MkNot(t)
    member this.(-*) (t1: BitVecExpr) (t2: BitVecExpr) = match t1 with  // a-b === a + (0-b)
                                                                | Int 0 -> ctx.MkBVSub(t1, t2)
                                                                | t1 -> ctx.MkBVAdd(t1, ctx.MkBVSub(ctx.MkBV(0, n), t2))
    member this.(+*) (t1: BitVecExpr) (t2: BitVecExpr) = match (t1, t2) with
                                                                | (Int 0, (Int 0 as t)) -> t 
                                                                | (Int 0, t) -> t
                                                                | (t, Int 0) -> t
                                                                | (t1, t2) -> ctx.MkBVAdd(t1, t2)
    member this.(=*) (t1: BitVecExpr) (t2: BitVecExpr) = ctx.MkEq(t1, t2)
    member this.(<=*) (t1: BitVecExpr) (t2: BitVecExpr) = ctx.MkBVULE(t1, t2)
    member this.(>=*) (t1: BitVecExpr) (t2: BitVecExpr) = ctx.MkBVUGE(t1, t2)
    member this.(>*) (t1: BitVecExpr) (t2: BitVecExpr) = ctx.MkBVUGT(t1, t2)
    member this.(<*) (t1: BitVecExpr) (t2: BitVecExpr) = ctx.MkBVULT(t1, t2)
    
    member this.contains (t: Expr) (var: BitVecExpr) =
        let var_name = var.FuncDecl.Name
        match t with
            | Var name -> var_name.ToString()=name
            | :? BitVecExpr as t -> Array.fold (fun acc t -> acc || this.contains t var) false t.Args
            | :? BoolExpr as t -> Array.fold (fun acc t -> acc || this.contains t var) false t.Args
            | _ -> failwith "unexpected term" 

    member this.getRules conclusion (var: BitVecExpr) =
                    
        let (~-) = this.(~-)
        let (-*) = this.(-*)
        let (+*) = this.(+*)
        let (<=*) = this.(<=*)
        let (<*) = this.(<*)
        let (>=*) = this.(>=*)
        let (>*) = this.(>*)
        let (=*) = this.(=*)
        

        let _0 = ctx.MkBV(0, n)
        let _1 = ctx.MkBV(1, n)

        let var_check t y z = this.contains t var && not (this.contains y var) && not (this.contains z var)
        let var_check2 t1 t2 y = this.contains t1 var && this.contains t2 var && not (this.contains y var)
        // t(x) - a terms containing x, y/z - x-free terms, a/b - any term
        match conclusion with
            | (Le(Plus(t, y), z) | Le(Plus(y, t), z) | Ge(z, Plus(t, y)) | Ge(z, Plus(y, t)))
                    when var_check t y z -> [
                [t <=* z-*y; y <=* z] // add1
                [t <=* z-*y; _0-*y <=* t] // add2 
                [_0-*y <=* t; y <=* z; -(y =* _0)] // add3
              ]
            | (Ge(Plus(t, y), z) | Ge(Plus(y, t), z) | Le(z, Plus(t, y)) | Le(z, Plus(y, t)))
                    when var_check t y z -> [
                [t >=* z-*y; z <=* y-*_1]; // add4
                [t >=* z-*y; t <=* _0-*y-*_1; -(y =* _0)] // add5 
                [y =* _0; z <=* t] // add6
                [-(y =* _0); z <=* y-*_1; var <=* _0-*y-*_1] // add7
              ]
            | ( Le(Plus(t1, y), t2) | Le(Plus(y, t1), t2) | Ge(t2, Plus(t1, y)) | Ge(t2, Plus(y, t1)) )
                    when var_check2 t1 t2 y -> [
                [ y <=* t2 -* t1; t1 <=* t2; ]; // bothx1
                [ y <=* t2 -* t1; _0-*t1 <=* y; ];  // bothx2
                [ _0-*t1 <=* y; t1 <=* t2; -(t1 =* _0)] // bothx3
              ]
            | Equals(a, b) -> [ [a <=* b; b <=* a] ] // eq
            | Not(Equals(a, b)) -> [ [a <* b];  [a >* b]  ] // neq
            | Not(Le(a, b)) -> [ [b <=* a-*_1; _1 <=* a] ] // nule
            | (Le(Minus(_0, t), y) | Ge(y, Minus(_0, t))) when var_check2 t t y -> [ [_0-*y <=* t] ] // inv
            | (Le(y, Minus(_0, t)) | Ge(Minus(_0, t), y)) when var_check2 t t y -> [ [t <=* _0-*y] ] // inv
            | Le(Mult(Int k1, Var x), Mult(Int k2, Var _x)) when x=var.FuncDecl.Name.ToString() && _x=var.FuncDecl.Name.ToString()
             -> [ [var <=* ctx.MkBV( ((pown 2 nn) * k1 / k2), n) ] ] // bothx4
            | _ -> []
     

    member this.Rewrite cube (var: BitVecExpr) model = // normalization procedure
        let (|=) (M: Map<Expr, Expr>) (F: BoolExpr) =
            let solver = ctx.MkSolver()
            solver.Check([| F.Substitute( (M |> Map.toArray |> Array.map fst), ( M |> Map.toArray |> Array.map snd ) ) |]) = Status.SATISFIABLE
    
        let False = ctx.MkFalse()
        let True = ctx.MkTrue()
        let Var = match var with Var t1 -> t1 | _ -> failwith "var must be a variable"
        // todo: assert cube is cube
        // todo: assert model |= cube
        match cube with
            | cube when not (this.contains cube var) -> cube
            | (Le(_, Mult(Int _, Var x)) | Ge(Mult(Int _, Var x), _)) when x=Var -> cube
            | (Le(_, Var x) | Ge(Var x, _)) when x=Var -> cube
            | (Le(Mult(Int _, Var x), _) | Ge(_, Mult(Int _, Var x)))  when x=Var -> cube
            | (Le(Var x, _) | Ge(_, Var x))  when x=Var -> cube
            | cube -> let list = this.getRules cube var
                      if List.length list = 0 then
                          False
                      else
                          let p = List.tryPick (fun _premises -> (List.fold (fun result p ->
                                                                                if result.IsNone then
                                                                                    None
                                                                                else
    //                                                                                printfn "%s %s" (String('_', i)) (formula_to_str p)
                                                                                    let e = this.Rewrite p var model
                                                                                    let conjuncts = match e with
                                                                                                        | CONJ args -> Array.toList args
                                                                                                        | t -> [t]
                                                                                    
                                                                                    if result.IsSome && model |= e then
                                                                                        Some (conjuncts @ result.Value)
                                                                                    else
    //                                                                                    printfn "%s failed %s" (String('_', i)) (formula_to_str (ctx.MkAnd(result.Value, q)))
                                                                                        None
                                                                                    ) (Some []) _premises)) list
                          match p with
                                | Some conjuncts -> ctx.MkAnd(conjuncts)
                                | None -> False
                                      
                                          
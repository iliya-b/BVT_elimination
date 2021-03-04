module BVTProver.Z3Patterns

open System.ComponentModel.Design
open Microsoft.Z3

let get_bvt_args (expr: Expr) =
    match expr.Args.[0], expr.Args.[1] with
        | :? BitVecExpr as t1, (:? BitVecExpr as t2) -> Some (t1, t2)
        | _ -> None
let get_bool_args (expr: Expr) =
    match expr.Args.[0], expr.Args.[1] with
        | :? BoolExpr as t1, (:? BoolExpr as t2) -> Some (t1, t2)
        | _ -> None
        
let (|ZTrue|_|) (expr: Expr) = if expr.IsTrue then Some() else None
let (|ZFalse|_|) (expr: Expr) = if expr.IsFalse then Some() else None

let (|ZCONJ|_|) (expr: Expr) =
    if expr.IsAnd then
        Some (Array.map (fun (e: Expr) -> e :?> BoolExpr) expr.Args)
    else
        None

let (|ZDISJ|_|) (expr: Expr) = if expr.IsOr then Some expr.Args else None

let (|ZNot|_|) (expr: Expr) = if expr.IsNot && expr.NumArgs = 1u 
                              then Some(expr.Args.[0]) else None

let (|ZIff|_|) (expr: Expr) = if expr.IsIff && expr.NumArgs = 2u 
                              then get_bool_args expr else None
let (|ZImplies|_|) (expr: Expr) = if expr.IsImplies && expr.NumArgs = 2u 
                                  then get_bool_args expr else None
               
let (|ZMinus|_|) (expr: Expr) = if expr.IsBVSub then get_bvt_args expr else None
                  
let (|ZPlus|_|) (expr: Expr) = if expr.IsBVAdd then get_bvt_args expr else None
let (|ZMult|_|) (expr: Expr) = if expr.IsBVMul then get_bvt_args expr else None

let (|ZVar|_|) (expr: Expr) =
    if expr.IsConst || expr.IsVar then
        Some (expr.ToString().Replace("|", ""))
    else
        None
let (|ZInt|_|) (expr: Expr) =
    if expr.IsBV && expr.IsNumeral then
        match expr with
         | :? BitVecNum as t -> Some t.Int
         | _ -> None
    else
        None
let (|ZLe|_|) (expr: Expr) = if expr.IsBVULE then get_bvt_args expr else None
let (|ZLt|_|) (expr: Expr) = if expr.IsBVULT then get_bvt_args expr else None
let (|ZGe|_|) (expr: Expr) = if expr.IsBVUGE then get_bvt_args expr else None
let (|ZGt|_|) (expr: Expr) = if expr.IsBVUGT then get_bvt_args expr else None
let (|ZEquals|_|) (expr: Expr) = if expr.IsEq then get_bvt_args expr else None
let (|ZExists|_|) (expr: Expr) =
    match expr with
     | :? Quantifier as expr when expr.IsExistential ->
         Some (expr.BoundVariableNames.[0], expr.Body :?> BoolExpr)
     | _ -> None
                                    
let (|ZForAll|_|) (expr: Expr) =
    match expr with
    | :? Quantifier as expr when expr.IsUniversal -> get_bool_args expr
    | _ -> None


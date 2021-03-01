module BVTProver.Z3Patterns

open System.ComponentModel.Design
open Microsoft.Z3

    
let n = uint32 8

let args2 (expr: Expr) = match expr.Args.[0] with
                            | :? BitVecExpr as t -> Some (t, match expr.Args.[1] with
                                                                 | :? BitVecExpr as t -> t // todo
                                                                 | _ -> failwith "not bvt")
                            | _ -> failwith "not bvt"
let bool_args2 (expr: Expr) = match expr.Args.[0] with
                                 | :? BoolExpr as t -> Some (t, match expr.Args.[1] with
                                                                    | :? BoolExpr as t -> t // todo
                                                                    | _ -> failwith "not bvt")
                                 | _ -> failwith "not bvt"
let (|ZTrue|_|) (expr: Expr) = if expr.IsTrue then Some() else None
let (|ZFalse|_|) (expr: Expr) = if expr.IsFalse then Some() else None

let (|ZCONJ|_|) (expr: Expr) = if expr.IsAnd then Some (Array.map (fun (e: Expr) -> e :?> BoolExpr) expr.Args) else None
let (|And|_|) (expr: Expr) = if expr.IsAnd && expr.NumArgs = 2u then bool_args2 expr else None
let (|ZDISJ|_|) (expr: Expr) = if expr.IsOr then Some expr.Args else None
let (|ZOr|_|) (expr: Expr) = if expr.IsOr && expr.NumArgs = 2u then bool_args2 expr else None
let (|ZNot|_|) (expr: Expr) = if expr.IsNot && expr.NumArgs = 1u 
                              then Some(expr.Args.[0]) else None

let (|ZIff|_|) (expr: Expr) = if expr.IsIff && expr.NumArgs = 2u 
                              then bool_args2 expr else None
let (|ZImplies|_|) (expr: Expr) = if expr.IsImplies && expr.NumArgs = 2u 
                                  then bool_args2 expr else None
               
let (|ZMinus|_|) (expr: Expr) = if expr.IsBVSub then args2 expr else None
                  
let (|ZPlus|_|) (expr: Expr) = if expr.IsBVAdd then
                                args2 expr
                               else
                                  None
let (|ZMult|_|) (expr: Expr) = if expr.IsBVMul then args2 expr else None

let (|ZVar|_|) (expr: Expr) =
    let get_var (expr: Expr) =
        if expr.IsConst || expr.IsVar then Some (expr.ToString().Replace("|", ""))
        else None
    match expr with
        | expr -> get_var expr
let (|ZInt|_|) (expr: Expr) = if expr.IsBV && expr.IsNumeral then match expr with
                                                                     | :? BitVecNum as t -> Some t.Int
                                                                     | _ -> None
                              else None // expr.Args.[0] todo
let (|ZLe|_|) (expr: Expr) = if expr.IsBVULE then args2 expr else None
let (|ZLt|_|) (expr: Expr) = if expr.IsBVULT then args2 expr else None
let (|ZGe|_|) (expr: Expr) = if expr.IsBVUGE then args2 expr else None
let (|ZGt|_|) (expr: Expr) = if expr.IsBVUGT then args2 expr else None
let (|ZEquals|_|) (expr: Expr) = if expr.IsEq then args2 expr else None
let (|ZExists|_|) (expr: Expr) = match expr with
                                    | :? Quantifier as expr when expr.IsExistential -> Some (expr.BoundVariableNames.[0], expr.Body :?> BoolExpr)
                                    | _ -> None
                                    
let (|ZForAll|_|) (expr: Expr) = match expr with // todo
                                    | :? Quantifier as expr when expr.IsUniversal -> bool_args2 expr
                                    | _ -> None


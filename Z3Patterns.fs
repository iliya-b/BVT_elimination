module BVTProver.Z3Patterns

open System
open System.Collections
open System.ComponentModel
open System.ComponentModel.Design
open Microsoft.Z3
open Helpers

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
        (Array.map (fun (e: Expr) -> e :?> BoolExpr) expr.Args) |> Some
    else
        None

let (|ZDISJ|_|) (expr: Expr) =
    if expr.IsOr then
        (Array.map (fun (e: Expr) -> e :?> BoolExpr) expr.Args) |> Some
    else
        None

let (|ZNot|_|) (expr: Expr) = if expr.IsNot && expr.NumArgs = 1u 
                              then Some(expr.Args.[0] :?> BoolExpr) else None

let (|ZIff|_|) (expr: Expr) = if expr.IsIff && expr.NumArgs = 2u 
                              then get_bool_args expr else None
let (|ZImplies|_|) (expr: Expr) = if expr.IsImplies && expr.NumArgs = 2u 
                                  then get_bool_args expr else None
               
let (|ZMinus|_|) (expr: Expr) = if expr.IsBVSub then get_bvt_args expr else None
                  
let (|ZPlus|_|) (expr: Expr) = if expr.IsBVAdd then get_bvt_args expr else None
let (|ZMult|_|) (expr: Expr) = if expr.IsBVMul then get_bvt_args expr else None
let (|ZBVOr|_|) (expr: Expr) = if expr.IsBVOR then get_bvt_args expr else None
let (|ZBVAnd|_|) (expr: Expr) = if expr.IsBVAND then get_bvt_args expr else None
let (|ZBVShL|_|) (expr: Expr) = if expr.IsBVShiftLeft then get_bvt_args expr else None
let (|ZBVShR|_|) (expr: Expr) = if expr.IsBVShiftRightLogical then get_bvt_args expr else None
let (|ZBVZeroEx|_|) (expr: Expr) = if expr.IsBVZeroExtension then Some (expr.Args.[0] :?> BitVecExpr, expr.FuncDecl.Parameters.[0].Int) else None
let (|ZExtract|_|) (expr: Expr) = if expr.IsBVExtract then Some (expr.Args.[0] :?> BitVecExpr, expr.FuncDecl.Parameters.[0].Int, expr.FuncDecl.Parameters.[1].Int) else None

let (|ZVar|_|) (expr: Expr) =
    if expr.IsConst || expr.IsVar then
        Some (expr.ToString().Replace("|", ""))
    else
        None
let (|ZInt|_|) (expr: Expr) =
    if expr.IsBV && expr.IsNumeral then
        match expr with
         | :? BitVecNum as t when t.IsInt -> Some t.UInt
         | _ -> None
    else
        None
let (|ZBV|_|) (expr: Expr) =
    if expr.IsBV && expr.IsNumeral then
        match expr with
         | :? BitVecNum as t when not t.IsInt ->
             Some (BitArray(t.BigInteger.ToByteArray()))
         | _ -> None
    else
        None
        

let (|ZLe|_|) (expr: Expr) =
    if expr.IsBVULE then expr |> get_bvt_args
    elif expr.IsBVUGE then expr |> get_bvt_args |> reverse_some_tuple
    else None
    
let (|ZLt|_|) (expr: Expr) =
    if expr.IsBVULT then expr |> get_bvt_args
    elif expr.IsBVUGT then expr |> get_bvt_args |> reverse_some_tuple
    else None
    
let (|ZSLe|_|) (expr: Expr) =
    if expr.IsBVSLE then expr |> get_bvt_args
    elif expr.IsBVSGE then expr |> get_bvt_args |> reverse_some_tuple
    else None
    
let (|ZSLt|_|) (expr: Expr) =
    if expr.IsBVSLT then expr |> get_bvt_args
    elif expr.IsBVSGT then expr |> get_bvt_args |> reverse_some_tuple
    else None
    


// todo: eliminate ZGe/ZGt
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


//type ZOperation =
//    | Binary of Expr*Expr
//    | Unary of Expr
//    | Mult of Expr list
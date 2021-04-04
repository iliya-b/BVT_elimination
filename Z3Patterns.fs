module BVTProver.Z3Patterns

open System
open System.Collections
open Microsoft.Z3
open Helpers
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

let (|ZXOR|_|) (expr: Expr) =
    if expr.IsXor then
        (Array.map (fun (e: Expr) -> e :?> BoolExpr) expr.Args) |> Some
    else
        None
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

let (|ZIff|_|) (expr: Expr) =
    if expr.IsIff && expr.NumArgs = 2u then
        get_bool_args expr
    elif expr.IsEq then
        match expr.Args with
        | [| :? BoolExpr ; :? BoolExpr  |] -> get_bool_args expr
        | _ -> None
    else
        None
let (|ZImplies|_|) (expr: Expr) = if expr.IsImplies && expr.NumArgs = 2u 
                                  then get_bool_args expr else None
                                 
let (|ZPlus|_|) (expr: Expr) = if expr.IsBVAdd then get_bvt_args expr else None
let (|ZSub|_|) (expr: Expr) = if expr.IsBVSub then get_bvt_args expr else None
let (|ZNeg|_|) (expr: Expr) = if  expr.IsBVUMinus then expr.Args.[0] :?> BitVecExpr |> Some else None
let (|ZMult|_|) (expr: Expr) = if expr.IsBVMul then get_bvt_args expr else None
let (|ZUDiv|_|) (expr: Expr) = if expr.IsBVUDiv then get_bvt_args expr else None
let (|ZBVComp|_|) (expr: Expr) = if expr.IsBVComp then get_bvt_args expr else None
let (|ZSDiv|_|) (expr: Expr) = if expr.IsBVSDiv then get_bvt_args expr else None
let (|ZURem|_|) (expr: Expr) = if expr.IsBVURem then get_bvt_args expr else None
let (|ZSRem|_|) (expr: Expr) = if expr.IsBVSRem then get_bvt_args expr else None
let (|ZSMod|_|) (expr: Expr) = if expr.IsBVSMod then get_bvt_args expr else None
let (|ZBVOr|_|) (expr: Expr) = if expr.IsBVOR then get_bvt_args expr else None
let (|ZBVXor|_|) (expr: Expr) = if expr.IsBVXOR then get_bvt_args expr else None
let (|ZBVNot|_|) (expr: Expr) = if expr.IsBVNOT then  Some (expr.Args.[0] :?> BitVecExpr) else None
let (|ZBVAnd|_|) (expr: Expr) = if expr.IsBVAND then get_bvt_args expr else None
let (|ZBVShL|_|) (expr: Expr) = if expr.IsBVShiftLeft then get_bvt_args expr else None
let (|ZBVShR|_|) (expr: Expr) = if expr.IsBVShiftRightLogical then get_bvt_args expr else None
let (|ZBVShRArith|_|) (expr: Expr) = if expr.IsBVShiftRightArithmetic then get_bvt_args expr else None
let (|ZBVZeroEx|_|) (expr: Expr) = if expr.IsBVZeroExtension then Some (expr.Args.[0] :?> BitVecExpr, expr.FuncDecl.Parameters.[0].Int) else None
let (|ZExtract|_|) (expr: Expr) = if expr.IsBVExtract then Some (expr.Args.[0] :?> BitVecExpr, expr.FuncDecl.Parameters.[0].Int, expr.FuncDecl.Parameters.[1].Int) else None

let (|ZVar|_|) (expr: Expr) =
    if (expr.IsConst || expr.IsVar) && not expr.IsBool then
           Some (expr.ToString().Replace("|", ""), (expr :?> BitVecExpr).SortSize)
    else
        None
let (|ZInt|_|) (expr: Expr) =
    if expr.IsBV && expr.IsNumeral && not expr.IsBool then
        match expr with
         | :? BitVecNum as t ->
             if t.SortSize=0u then
                unexpected ()
             else
                Some (t.UInt, t.SortSize)
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


let (|ZITE|_|) (expr: Expr) = if expr.IsITE then Some (expr.Args.[0] :?> BoolExpr, expr.Args.[1]  :?> BitVecExpr, expr.Args.[2] :?> BitVecExpr) else None
let (|ZDistinct|_|) (expr: Expr) = if expr.IsDistinct then Some () else None
let (|ZConcat|_|) (expr: Expr) = if expr.IsBVConcat then get_bvt_args expr else None
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

let private is_LIA_term_z3 term =
    let rec Loop (allow_vars: bool) acc term =

        let continuation a b = Loop allow_vars (fun a -> a && Loop allow_vars acc b) a 
        match term with
         | ZVar _ when not allow_vars -> false
         | ZInt _
         | ZVar _ ->  acc true
         | ZSub(a,b)
         | ZPlus (a, b)
         | ZMult (a, b)  -> continuation a b
         | ZNeg a -> Loop allow_vars acc a
         | ZUDiv (a, b) -> Loop allow_vars (fun a -> a && Loop false acc b) a  // allow division by a constant
         | ZSDiv _ -> false
         | ZUDiv _ | ZSDiv _ -> false
         | ZExtract _
         | ZConcat _ 
         | ZBVShL _ 
         | ZBVShR _ 
         | ZBVShRArith _ 
         | ZBVZeroEx _ 
         | ZBVAnd _ | ZBVOr _ | ZBVXor _ | ZBVNot _  -> false
         | ZSRem _ | ZURem _ | ZSMod _ | ZBVComp _ -> false
         | t when (t.IsBool) -> false
         | t when t.IsBVSignExtension || t.IsITE -> false
         | t -> false
    Loop true (fun x -> x) term
let rec is_LIA_z3 formula =
    let is_LIA_term = is_LIA_term_z3
    let is_LIA_formula = is_LIA_z3
    match formula with
    | ZCONJ args
    | ZDISJ args
    | ZXOR args -> Array.forall is_LIA_formula args
    | ZEquals (t1, t2)
    | ZLe (t1, t2)
    | ZSLe (t1, t2)
    | ZLt (t1, t2)
    | ZSLt (t1, t2) -> is_LIA_term t1 && is_LIA_term t2
    | ZImplies (t1, t2)
    | ZIff (t1, t2) -> is_LIA_formula t1 && is_LIA_formula t2
    | ZExists (_, t)
    | ZNot t -> is_LIA_formula t
    | ZFalse
    | ZTrue -> true
    | ZDistinct _ -> false
    | f when (f.IsBool && f.IsConst) || f.IsITE -> false
    | f -> false
    



let rec private z3_depth_term (acc: int) term =
    if acc >= 100 then
        acc
    else
        let z3_depth_term = z3_depth_term (acc+1)
        match term with
         | ZInt _
         | ZVar _ -> acc
         | ZMult (a, b)  -> Math.Max  (z3_depth_term a, z3_depth_term b)
         | ZNeg a
         | ZUDiv (a, ZInt _) -> z3_depth_term a // allow division by a constant
         | ZUDiv (a, b) | ZSDiv (a, b) 
         | ZSub(a,b) | ZPlus (a, b)  -> Math.Max (z3_depth_term a, z3_depth_term b)
         | ZITE (c, a, b) -> Math.Max (z3_depth_term a, z3_depth_term b)
         | ZExtract _
         | ZConcat _ 
         | ZBVShL _ 
         | ZBVShR _ 
         | ZBVShRArith _ 
         | ZBVZeroEx _ 
         | ZBVAnd _ | ZBVOr _ | ZBVXor _ | ZBVNot _  
         | ZSRem _ | ZURem _ | ZSMod _ -> failwith "not lia"
         | t when t.IsBVSignExtension -> failwith "not lia"
let rec z3_depth_formula acc formula =
    let z3_depth_formula = z3_depth_formula (acc + 1)
    let z3_depth_term = z3_depth_term (acc + 1)
    match formula with
    | ZCONJ args
    | ZDISJ args
    | ZXOR args -> Array.map z3_depth_formula args |> Array.max
    | ZEquals (t1, t2)
    | ZLe (t1, t2)
    | ZSLe (t1, t2)
    | ZLt (t1, t2)
    | ZSLt (t1, t2) -> Math.Max(z3_depth_term t1, z3_depth_term t2)
    | ZImplies (t1, t2)
    | ZIff (t1, t2) -> Math.Max(z3_depth_formula t1, z3_depth_formula t2)
    | ZExists (_, t)
    | ZNot t -> z3_depth_formula t
    | ZFalse
    | ZTrue -> acc
    | f when f.IsBool && f.IsConst -> failwith "not lia"
    | f ->
        let ss = f.ToString()
        failwith ss





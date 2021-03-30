module BVTProver.Z3Patterns

open System
open System.Collections
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
let (|ZUDiv|_|) (expr: Expr) = if expr.IsBVUDiv then get_bvt_args expr else None
let (|ZSDiv|_|) (expr: Expr) = if expr.IsBVSDiv then get_bvt_args expr else None
let (|ZURem|_|) (expr: Expr) = if expr.IsBVURem then get_bvt_args expr else None
let (|ZSRem|_|) (expr: Expr) = if expr.IsBVSRem then get_bvt_args expr else None
let (|ZSMod|_|) (expr: Expr) = if expr.IsBVSMod then get_bvt_args expr else None
let (|ZBVOr|_|) (expr: Expr) = if expr.IsBVOR then get_bvt_args expr else None
let (|ZBVAnd|_|) (expr: Expr) = if expr.IsBVAND then get_bvt_args expr else None
let (|ZBVShL|_|) (expr: Expr) = if expr.IsBVShiftLeft then get_bvt_args expr else None
let (|ZBVShR|_|) (expr: Expr) = if expr.IsBVShiftRightLogical then get_bvt_args expr else None
let (|ZBVZeroEx|_|) (expr: Expr) = if expr.IsBVZeroExtension then Some (expr.Args.[0] :?> BitVecExpr, expr.FuncDecl.Parameters.[0].Int) else None
let (|ZExtract|_|) (expr: Expr) = if expr.IsBVExtract then Some (expr.Args.[0] :?> BitVecExpr, expr.FuncDecl.Parameters.[0].Int, expr.FuncDecl.Parameters.[1].Int) else None

let (|ZVar|_|) (expr: Expr) =
    if (expr.IsConst || expr.IsVar) && not expr.IsBool then
           Some (expr.ToString().Replace("|", ""), (expr :?> BitVecExpr).SortSize)
    else
        None
let (|ZInt|_|) (expr: Expr) =
    if expr.IsBV && expr.IsNumeral then
        match expr with
         | :? BitVecNum as t -> Some (t.UInt, t.SortSize)
         | _ -> None
    else
        None
        
        
let (|ZBV|_|) (expr: Expr) =
    if expr.IsBV && expr.IsNumeral then
        match expr with
         | :? BitVecNum as t ->
             let k = t.ToString()
             
             try
                 let arr = t.BigInteger.ToByteArray()

                 let bits = BitArray arr
                 
                 if BitConverter.IsLittleEndian then
                     let length = bits.Length;
                     let mid = (length / 2);

                     for i = 0 to mid-1 do // reverse bits to get BigEndian
                        let bit = bits.[i]
                        bits.[i] <- bits.[length - i - 1]
                        bits.[length - i - 1] <- bit
                    
                 let number_length = bits.Length
                 let vector_length = int t.SortSize
                 let offset = vector_length - number_length
                 
                 if offset = 0 then 
                     Some (bits)
                 elif offset > 0 then
                     let full_vector = BitArray vector_length

                     for i = 0 to number_length-1 do
                         full_vector.[i+offset] <- bits.[i]
                         
                     Some full_vector
                 else
                     let full_vector = BitArray vector_length

                     for i = 0 to vector_length-1 do
                         full_vector.[vector_length-1-i] <- bits.[number_length-1-i]
                         
                     Some full_vector
             with
               | :? Microsoft.Z3.Z3Exception ->
                   printf "hmm"
                   Some (BitArray 0) // todo ???
                
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
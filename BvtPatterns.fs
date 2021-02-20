module BVTProver.BvtPatterns

open System.ComponentModel.Design
open Microsoft.Z3

let n = uint32 8

let _or f1 f2 = fun e -> f1 e || f2 e 

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
let (|True|_|) (expr: Expr) = if expr.IsTrue then Some() else None
let (|False|_|) (expr: Expr) = if expr.IsFalse then Some() else None

let (|CONJ|_|) (expr: Expr) = if expr.IsAnd then Some (Array.map (fun (e: Expr) -> e :?> BoolExpr) expr.Args) else None

let (|And|_|) (expr: Expr) = if expr.IsAnd && expr.NumArgs = 2u then bool_args2 expr else None
let (|DISJ|_|) (expr: Expr) = if expr.IsOr then Some expr.Args else None
let (|Or|_|) (expr: Expr) = if expr.IsOr && expr.NumArgs = 2u then bool_args2 expr else None
let (|Not|_|) (expr: Expr) = if expr.IsNot && expr.NumArgs = 1u 
                             then Some(expr.Args.[0]) else None

let (|Iff|_|) (expr: Expr) = if expr.IsIff && expr.NumArgs = 2u 
                             then bool_args2 expr else None
let (|Implies|_|) (expr: Expr) = if expr.IsImplies && expr.NumArgs = 2u 
                                 then bool_args2 expr else None
               
let (|Minus|_|) (expr: Expr) = if expr.IsBVSub then args2 expr else None
                  
let (|Plus|_|) (expr: Expr) = if expr.IsBVAdd then
                                args2 expr
                              else
                                  None
let (|Mult|_|) (expr: Expr) = if expr.IsBVMul then args2 expr else None

let (|Var|_|) (expr: Expr) =
    let get_var (expr: Expr) =
        if expr.IsConst || expr.IsVar then Some (if expr.IsFuncDecl then
                                                     expr.FuncDecl.Name.ToString().Replace("|", "")
                                                 else
                                                     expr.ToString().Replace("|", ""))
        else None
    match expr with
        | expr -> get_var expr
        

    
let rec contains (t: Expr) (var: Expr) =
        let var_name = var.FuncDecl.Name
        match t with
            | Var name -> var_name.ToString()=name
            | :? BitVecExpr as t -> Array.fold (fun acc t -> acc || contains t var) false t.Args
            | :? BoolExpr as t -> Array.fold (fun acc t -> acc || contains t var) false t.Args
            | _ -> failwith "unexpected term" 


let (|Int|_|) (expr: Expr) = if expr.IsBV && expr.IsNumeral then match expr with
                                                                     | :? BitVecNum as t -> Some t.Int
                                                                     | _ -> None
                             else None // expr.Args.[0] todo
let (|Le|_|) (expr: Expr) = if expr.IsBVULE then args2 expr else None
let (|Lt|_|) (expr: Expr) = if expr.IsBVULT then args2 expr else None
let (|Ge|_|) (expr: Expr) = if expr.IsBVUGE then args2 expr else None
let (|Gt|_|) (expr: Expr) = if expr.IsBVUGT then args2 expr else None
let (|Equals|_|) (expr: Expr) = if expr.IsEq then args2 expr else None
let (|Exists|_|) (expr: Expr) = match expr with
                                    | :? Quantifier as expr when expr.IsExistential -> Some (expr.BoundVariableNames.[0], expr.Body :?> BoolExpr)
                                    | _ -> None
                                    
let (|ForAll|_|) (expr: Expr) = match expr with // todo
                                    | :? Quantifier as expr when expr.IsUniversal -> bool_args2 expr
                                    | _ -> None
let (|ThisVar|_|) (this_var: Expr) (expr: Expr) =
    match expr with
        | (Var X) as var -> Some var
        | _ -> None
        
let (|ConstMultiplication|_|) (expr: Expr) (var: Expr) = 
        match expr with
            | Mult (Int _, ThisVar var _)
            | Mult (ThisVar var _, Int _) 
            | ThisVar var _ -> Some()
            | _ -> None
            
let (|LIA_1|_|) (x: Expr) (expr: Expr)  =     
    let is_trivial_inequality (conjunct: Expr) =
        match conjunct with
            | Le(ConstMultiplication x, _) -> true
            | _ -> false
            
    let is_free (conjunct: Expr) = not (contains conjunct x)
    
    let is_acceptable = _or is_free is_trivial_inequality
    
    match expr with
        | CONJ args when Array.forall is_acceptable args -> Some (Array.partition is_free args)
        | _ -> None
        
let (|LIA_2|_|) (x: Expr) (expr: Expr)  = 
    
    let is_inequality (conjunct: Expr) =
        match conjunct with
            | Le(ConstMultiplication x, _) -> true
            | Lt(_, ConstMultiplication x) -> true
            | _ -> false
    let is_free (conjunct: Expr) = not (contains conjunct x)
        
    match expr with
        | CONJ args when Array.forall (_or is_inequality is_free) args -> Some args
        | _ -> None
        
let (|LIA_3|_|) (x: Expr) (expr: Expr)  = 
    
    let is_inequality (conjunct: Expr) =
        match conjunct with
            | Le(ConstMultiplication x, _) -> true
            | Lt(_, ConstMultiplication x) -> true
            | _ -> false
    let is_free (conjunct: Expr) = not (contains conjunct x)
        
    match expr with
        | CONJ args when Array.forall (_or is_inequality is_free) args -> Some args
        | _ -> None
        
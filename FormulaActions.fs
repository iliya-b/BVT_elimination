module BVTProver.FormulaActions


open BVTProver
open Formula
open Z3Patterns
open Microsoft.Z3
open Helpers
open Continuations

type Expression =
    | Formula of Formula
    | Term of Term

let rec is_LIA_term term =
    match term with
     | Int _
     | Var _ -> true
     | Mult (a, Int _) 
     | Mult (Int _, a)  -> is_LIA_term a // allow multiplication by a constant
     | Mult _ -> false
     | Div (a, Int _) -> is_LIA_term a // allow division by a constant
     | Div _ -> false
     | Plus (a, b)  -> (is_LIA_term a) && (is_LIA_term b)
     | Inv a -> is_LIA_term a
     | Extract _ -> false
     | _ -> false
let rec is_LIA_formula formula =
    match formula with
    | And args
    | Or args -> List.forall is_LIA_formula args
    | Equals (t1, t2)
    | Le (t1, t2)
    | SLe (t1, t2)
    | Lt (t1, t2)
    | SLt (t1, t2) -> is_LIA_term t1 && is_LIA_term t2
    | Implies (t1, t2)
    | Iff (t1, t2) -> is_LIA_formula t1 && is_LIA_formula t2
    | Exists (_, t)
    | Not t -> is_LIA_formula t
    | False
    | True -> true


let rec term_contains var term =
    let contains = term_contains var
    match term with
    | t when t = var -> true
    | Mult (t1, t2)
    | Plus (t1, t2) -> contains t1 || contains t2
    | Div (t1, t2) -> contains t1 || contains t2
    | Extract (t, _, _) -> contains t
    | Inv t -> contains t
    | Integer _
    | Var _ -> false
    | _ -> failwith "unexpected term"

let rec formula_contains var expr =
    let contains = formula_contains var
    let term_contains = term_contains var
    match expr with
    | And args
    | Or args -> List.exists contains args
    | Equals (t1, t2)
    | Le (t1, t2)
    | Lt (t1, t2) -> term_contains t1 || term_contains t2
    | Implies (t1, t2)
    | Iff (t1, t2) -> contains t1 || contains t2
    | Exists (_, t)
    | Not t -> contains t
    | _ -> false
let as_term = function | Term t -> t | _ -> unexpected ()
let as_formula = function | Formula t -> t | _ -> unexpected ()


let z3_mapper e =
    
    let bin_bunch op (t1: Expr) (t2: Expr) =  Bin ((fun e1 e2 -> Formula (op (as_formula e1, as_formula e2))), t1, t2)
    let bin_predicate op (t1: Expr) t2 =  Bin ((fun e1 e2 -> Formula (op (as_term e1, as_term e2))), t1, t2)
    let bin_op op (t1: Expr) t2 =  Bin ((fun e1 e2 -> Term (op (as_term e1, as_term e2))), t1, t2)
    let unary_bool op (t: Expr) =  Unary ((fun e1 -> Formula (op (as_formula e1))), t)
    let unary_op op (t: Expr) =  Unary ((fun e1 -> Term (op (as_term e1))), t)
    let bool_array op args =  List ((fun lst -> Formula (op (List.map as_formula lst))), args |> List.ofArray |> List.map (fun e -> e:>Expr))
    
    match e with
        | ZEquals (t1, t2) -> bin_predicate Equals t1 t2
        | ZLe (t1, t2) -> bin_predicate Le t1 t2
        | ZLt (t1, t2) -> bin_predicate Lt t1 t2
        | ZSLe (t1, t2) -> bin_predicate SLe t1 t2
        | ZSLt (t1, t2) -> bin_predicate SLt t1 t2
        | ZCONJ args -> bool_array And args
        | ZDISJ args -> bool_array Or args
        | ZNot t -> unary_bool Not t
        | ZImplies (l, r) -> bin_bunch Implies l r
        | ZExists (var, t) ->  unary_bool (fun t -> Exists(Var (var.ToString(), 0u), t)) t
        | ZTrue -> Const (Formula True)
        | ZFalse -> Const (Formula False)
        | ZVar (name, s) -> Const (Term (Var (name, s)))
        | ZMult (t1, t2) ->  bin_op Mult t1 t2  
        | ZUDiv (t1, t2) ->  bin_op Div t1 t2  
        | ZSDiv (t1, t2) ->  bin_op Div t1 t2  // todo
        | ZURem (t1, t2) ->  bin_op (fun (a, b) -> a - (Div(a, b) * b)) t1 t2  
        | ZPlus (t1, t2) -> bin_op Plus t1 t2  
        | ZBVAnd (t1, t2) -> bin_op BitAnd t1 t2  
        | ZBVOr (t1, t2) -> bin_op BitOr t1 t2  
        | ZBVShR (t1, t2) -> bin_op ShiftRightLogical t1 t2 
        | ZBVShL (t1, t2) -> bin_op ShiftLeft t1 t2  
        | ZInt (c, size) -> Const (Term (Integer (c, size)))
        | ZBVZeroEx (t, d) -> unary_op (fun t -> ZeroEx (t, d)) t 
        | ZExtract (t, a, b) -> unary_op (fun t -> Extract (t, a, b)) t
        | ZITE(t, a, b) -> Triple ((fun c e1 e2 -> Term (Ite (as_formula c, as_term e1, as_term e2))), t :> Expr, a :> Expr, b :> Expr)
        | t -> sprintf "unexpected z3 expression %O" t |> failwith
let formula_mapper _Equals _Le _Lt _SLe _SLt _And _Or
    _Implies _Iff _Exists _Not _True _False _Var _Mult
    _Plus _BitAnd _BitOr _ShiftRightLogical _ShiftLeft
    _BV _ZeroEx _Extract _Ite _Div _Inv e =
        
    let bin_bunch op t1 t2 = Bin (op, Formula t1, Formula t2)
    let bin_predicate op t1 t2 = Bin (op, Term t1, Term t2)
    let bin_op op t1 t2 = Bin (op, Term t1, Term t2)
    let unary_bool op t = Unary (op, Formula t)
    let unary_op op t = Unary (op, Term t)
    
    match e with
    | Formula f ->
        match f with  
        | Equals (t1, t2) -> bin_predicate _Equals t1 t2
        | Le (t1, t2) -> bin_predicate _Le t1 t2
        | Lt (t1, t2) -> bin_predicate _Lt t1 t2
        | SLe (t1, t2) -> bin_predicate _SLe t1 t2
        | SLt (t1, t2) -> bin_predicate _SLt t1 t2
        | And [a ; b] -> bin_bunch _And a b
        | Or [a ; b] -> bin_bunch _Or a b
        | Or [f]
        | And [f] -> unary_bool (fun x -> x) f
        | And (t1::tail) -> bin_bunch _And t1 (And tail)
        | Or  (t1::tail) -> bin_bunch _Or t1 (Or tail)
        | And [] | Or [] -> failwith "Empty And/Or"
        | Iff (t1, t2) -> bin_bunch _Iff t1 t2
        | Implies (t1, t2) -> bin_bunch _Implies t1 t2
        | Not (t) ->  unary_bool _Not t
        | Exists (Var (var, s), t) ->  unary_bool (fun t -> _Exists (_Var var s) t) t
        | True -> Const (_True)
        | False -> Const (_False)
        | Exists _ -> failwith "unexpected term as bounded variable"

    | Term t ->
        match t with
        | Var (name, s) -> Const (_Var name s)
        | Mult (t1, t2) ->  bin_op _Mult t1 t2
        | Div (t1, t2) ->  bin_op _Div t1 t2
        | Plus (t1, t2) -> bin_op _Plus t1 t2
        | BitAnd (t1, t2) -> bin_op _BitAnd t1 t2
        | BitOr (t1, t2) -> bin_op _BitOr t1 t2
        | ShiftRightLogical (t1, t2) -> bin_op _ShiftRightLogical t1 t2
        | ShiftLeft (t1, t2) -> bin_op _ShiftLeft t1 t2
        | Integer (c, size) -> Const (_BV c size)
        | Inv t -> unary_op _Inv t
        | ZeroEx (t, d) -> unary_op (fun t -> _ZeroEx t d) t
        | Extract (t, a, b) -> unary_op (fun t -> _Extract t a b) t
        | Ite(t, a, b) -> Triple ((fun c e1 e2 -> _Ite c e1 e2), Formula t, Term a, Term b)

        
        
let convert_z3 expr =
    let fold = fold z3_mapper (fun x -> x)
    let map = List.ofArray >> (List.map (fun e -> e:>Expr |> fold |> as_formula))
    match expr with  // expect a cube or a literal
    | ZCONJ args -> args |> map |> And |> Formula
    | ZDISJ args -> args |> map |> Or |> Formula
    | expr -> fold expr
let z3_formula_mapper (ctx: Context) =
        let as_bvt ((a, b): Expr*Expr) = (a :?> BitVecExpr, b :?> BitVecExpr)
        let as_bool ((a, b): Expr*Expr) = (a :?> BoolExpr, b :?> BoolExpr)
        let op Op a b = (a, b) |> as_bvt |> Op :> Expr
        let bool_op Op a b = (a, b) |> as_bool |> Op :> Expr
        formula_mapper
            (op ctx.MkEq)
            (op ctx.MkBVULE)
            (op ctx.MkBVULT)
            (op ctx.MkBVSLE)
            (op ctx.MkBVSLT)
            
            (fun a b -> ctx.MkAnd(a :?> BoolExpr, b :?> BoolExpr) :> Expr)
            (fun a b -> ctx.MkOr(a :?> BoolExpr, b :?> BoolExpr) :> Expr)
            
            (bool_op ctx.MkImplies)
            (bool_op ctx.MkIff)
            (fun a b -> ctx.MkExists([|a :?> BitVecExpr|], b :?> BoolExpr) :> Expr)
            (fun a -> a :?> BoolExpr |> ctx.MkNot :> Expr)
            (ctx.MkTrue() :> Expr)
            (ctx.MkFalse() :> Expr)
            (fun name s -> ctx.MkBVConst(name, s) :> Expr)
            (op ctx.MkBVMul)
            (op ctx.MkBVAdd)
            (op ctx.MkBVAND)
            (op ctx.MkBVOR)
            (op ctx.MkBVLSHR)
            (op ctx.MkBVSHL)
            (fun bits size -> (bits, size) |> ctx.MkBV :> Expr)
            (fun a d -> (uint32 d, a :?> BitVecExpr) |> ctx.MkZeroExt :> Expr)
            (fun t a b -> (uint32 a, uint32 b, t :?> BitVecExpr) |> ctx.MkExtract :> Expr)
            (fun condition _if _else -> ctx.MkITE(condition :?> BoolExpr, _if :?> BitVecExpr, _else :?> BitVecExpr))
            (op ctx.MkBVUDiv)
            (fun a -> a :?> BitVecExpr |> ctx.MkBVNeg :> Expr)

let z3fy_expression ctx = fold (z3_formula_mapper ctx) (fun x -> x)

let SmartDiv (a, b) = // simplify division
        match b with
        | Integer (1u, _) -> a
        | b -> Div (a, b)

let tuplify_list2 list =
    match list with
     | [a; b] -> (a, b)
     | _ -> failwith "cannot tuplify list"


let (|Contains|_|) x (e: Term) =
    if term_contains x e then Some(e) else None

let (|FreeOf|_|) (x: VarVector) (e: Term) =
    if not (term_contains (Var x) e) then Some(e) else None


let some_matches (|Pattern|_|) expressions =
        List.tryFind (function | Pattern _ -> true | _ -> false) expressions
let each_matches (|Pattern|_|) expressions =
         List.forall (function | Pattern _ -> true | _ -> false) expressions
        
let (|ThisVar|_|) (x: VarVector) (e: Term) =
    match e with
    | t when t = (Var x) -> Some()
    | _ -> None


let private get_model_z3 (ctx: Context) (expr: Expr) =    
    let solver = ctx.MkSolver()
    solver.Add (expr :?> BoolExpr)
    if solver.Check()=Status.SATISFIABLE then
        Some solver.Model
    else
        None
let private test_formula_z3 ctx = (get_model_z3 ctx)>>Option.isSome
    
let get_model f =
    let ctx = new Context()
    Formula f
    |> (z3fy_expression ctx)
    |> (get_model_z3 ctx)

let has_model = get_model>>Option.isSome
let is_tautology = Not>>get_model>>Option.isNone

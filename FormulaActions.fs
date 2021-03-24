module BVTProver.FormulaActions

open System.Collections.Generic
open BVTProver
open Formula
open Z3Patterns
open Microsoft.Z3
open Helpers
open Continuations

type Expression =
    | Formula of Formula
    | Term of Term

let rec interpret_term (M: IDictionary<string, uint32>) formula =
    let interpret_term = interpret_term M

    let d =
        match formula with
        | Var name -> M.[name]
        | Mult (t1, t2) -> (interpret_term t1) * (interpret_term t2)
        | Plus (t1, t2) -> (interpret_term t1) + (interpret_term t2)
        | Div (t1, d) -> (interpret_term t1) / (interpret_term d)
        | Inv t -> Term.MaxNumber - (interpret_term t)
        | Int c -> c
        | Extract(t, a, b) ->
            let d = (interpret_term t)
            let s = b - a + 1
            ((1u <<< s) - 1u) &&& (d >>> (a-1))

    d %% (Term.MaxNumber+1u)
let rec interpret_formula M formula: bool =
    let interpret_formula = interpret_formula M
    let interpret_term = interpret_term M

    match formula with
        | Not f -> interpret_formula  f
        | Iff (f1, f2) -> interpret_formula f1 && interpret_formula f2
        | Implies (f1, f2) -> not (interpret_formula f1) || interpret_formula f2
        | And args -> List.forall interpret_formula args
        | Or args -> List.exists interpret_formula args
        | Equals (a, b) -> interpret_term a = interpret_term b
        | Le (a, b) -> interpret_term a <= interpret_term b
        | Lt (a, b) -> interpret_term a < interpret_term b
        | Ge _
        | Gt _ -> failwith "use Le, Lt instead of Ge, Gt"
        | True -> true
        | False -> false 
        | Exists _ -> failwith "try to interpret quantified formula"

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
let rec is_LIA_formula formula =
    match formula with
    | And args
    | Or args -> List.forall is_LIA_formula args
    | Equals (t1, t2)
    | Le (t1, t2)
    | Lt (t1, t2)
    | Ge (t1, t2)
    | Gt (t1, t2) -> is_LIA_term t1 && is_LIA_term t2
    | Implies (t1, t2)
    | Iff (t1, t2) -> is_LIA_formula t1 && is_LIA_formula t2
    | Exists (_, t)
    | Not t -> is_LIA_formula t
    | _ -> false
     
let rec substitute_term (M: IDictionary<Term, Term>) term =
    let substitute_term = substitute_term M
    match term with
    | t when M.ContainsKey(t) -> M.[t]
    | Mult (t1, t2) -> Mult(substitute_term t1, substitute_term t2)
    | Plus (t1, t2) -> Plus(substitute_term t1, substitute_term t2)
    | Div (t1, d) -> Div(substitute_term t1, substitute_term d)
    | Inv t -> Inv(substitute_term t)
    | Extract (t, a, b) -> Extract(substitute_term t, a, b)
    | Int t -> Int t
    | Var t -> Var t

let rec substitute_formula (M: IDictionary<Term, Term>) formula =
         let substitute_formula = substitute_formula M
         let substitute_term = substitute_term M
         match formula with 
            | And args -> args |> (List.map substitute_formula) |> And
            | Or args -> args |> (List.map substitute_formula) |> Or
            | Equals (t1, t2) -> Equals(substitute_term t1, substitute_term t2) 
            | Le (t1, t2) ->  Le(substitute_term t1, substitute_term t2) 
            | Lt (t1, t2) ->  Lt(substitute_term t1, substitute_term t2) 
            | Ge (t1, t2) ->  Ge(substitute_term t1, substitute_term t2) 
            | Gt (t1, t2) -> Gt(substitute_term t1, substitute_term t2) 
            | Not t -> Not (substitute_formula t)
            | Implies (t1, t2) -> Implies(substitute_formula t1, substitute_formula t2) 
            | Iff (t1, t2) ->  Iff (substitute_formula t1, substitute_formula t2)
            | Exists(name, F) -> failwith "try to substitute terms on quantified formula"
            | (True | False) as constant -> constant 
            

let rec term_contains var term =
    let contains = term_contains var
    match term with
    | t when t = var -> true
    | Mult (t1, t2)
    | Plus (t1, t2) -> contains t1 || contains t2
    | Div (t1, t2) -> contains t1 || contains t2
    | Inv (t) -> contains t
    | Int _
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
    | Lt (t1, t2)
    | Ge (t1, t2)
    | Gt (t1, t2) -> term_contains t1 || term_contains t2
    | Implies (t1, t2)
    | Iff (t1, t2) -> contains t1 || contains t2
    | Exists (_, t)
    | Not t -> contains t
    | _ -> false


let rec z3fy_term (ctx: Context) expr =
    let z3fy = z3fy_term ctx
    match expr with
    | Var name -> ctx.MkBVConst(name, Term.Bits)
    | Mult (t1, t2) -> ctx.MkBVMul(z3fy t1, z3fy t2)
    | Plus (t1, Inv t2)
    | Plus (Inv t2, t1) -> ctx.MkBVSub(z3fy t1, z3fy t2)
    | Plus (t1, t2) -> ctx.MkBVAdd(z3fy t1, z3fy t2)
    | Div (t1, d) -> ctx.MkBVUDiv(z3fy t1, z3fy d)
    | Inv t -> ctx.MkBVNeg(z3fy t)
    | Extract (t, a, b ) -> ctx.MkExtract(uint32 a, uint32 b, z3fy t)
    | Int c -> ctx.MkBV(c, (if c=0u then 1u else Term.Bits)) :> BitVecExpr
let rec z3fy_formula (ctx: Context) formula: BoolExpr =
    let z3fy_formula = z3fy_formula ctx
    let z3fy_term = z3fy_term ctx

    let map_z3 args = args |> (List.map z3fy_formula) |> Array.ofList

    match formula with
    | And args -> ctx.MkAnd(map_z3 args)
    | Or args -> ctx.MkOr(map_z3 args)
    | Equals (t1, t2) -> ctx.MkEq(z3fy_term t1, z3fy_term t2)
    | Le (t1, t2) -> ctx.MkBVULE(z3fy_term t1, z3fy_term t2)
    | Lt (t1, t2) -> ctx.MkBVULT(z3fy_term t1, z3fy_term t2)
    | Ge (t1, t2) -> ctx.MkBVUGE(z3fy_term t1, z3fy_term t2)
    | Gt (t1, t2) -> ctx.MkBVUGT(z3fy_term t1, z3fy_term t2)
    | Implies (t1, t2) -> ctx.MkImplies(z3fy_formula t1, z3fy_formula t2)
    | Iff (t1, t2) -> ctx.MkIff(z3fy_formula t1, z3fy_formula t2)
    | Exists (t, t2) -> ctx.MkExists([| z3fy_term t |], z3fy_formula t2) :> BoolExpr
    | Not t -> ctx.MkNot(z3fy_formula t)
    | False -> ctx.MkFalse()
    | True -> ctx.MkTrue()
    | _ -> failwith "unexpected formula"
let a = (Mult)
let rec term_from_z3 (expr: BitVecExpr) =
    let rec Loop e acc =
        let binary_op_list typ l r = Loop l (fun lacc -> Loop r (fun racc -> acc (typ [lacc; racc])) )
        let binary_op typ l r = Loop l (fun lacc -> Loop r (fun racc -> acc (typ (lacc, racc))) )

        match e with
            
            | ZVar name -> Var name
            | ZMult (t1, t2) ->  binary_op Mult t1 t2 
            | ZPlus (t1, t2) -> binary_op Plus t1 t2 // Plus(term_from_z3 t1, term_from_z3 t2)
            | ZBVAnd (t1, t2) -> binary_op BitAnd t1 t2 // BitAnd(term_from_z3 t1, term_from_z3 t2)
            | ZBVOr (t1, t2) -> binary_op BitOr t1 t2 // BitOr(term_from_z3 t1, term_from_z3 t2)
            | ZBVShR (t1, t2) -> binary_op ShiftRightLogical t1 t2//  ShiftRightLogical(term_from_z3 t1, term_from_z3 t2)
            | ZBVShL (t1, t2) -> binary_op ShiftLeft t1 t2 //  ShiftLeft(term_from_z3 t1, term_from_z3 t2)
            | ZInt c -> Int c
            | ZBV c -> Int 0u
            | ZBVZeroEx (t, d) -> Loop t (fun tacc -> acc (ZeroEx (tacc, int d)))
            | ZExtract (t, a, b) -> Loop t (fun tacc -> acc (Extract (tacc, int a, int b)))
            | t ->
                    let descr = t.ToString()
                    failwith "unexpected z3 expression {t}"
    Loop expr (fun x -> x)


let as_term = function | Term t -> t | _ -> failwith "unexpected formula, expected: Term"
let as_formula = function | Formula t -> t | _ -> failwith "unexpected term, expected: Formula"

let z3_mapper e = 
    let And (a, b) = And [a ; b]
    let Or (a, b) = Or [a ; b]
    
    let bin_bunch op (t1: Expr) (t2: Expr) =  Bin ((fun e1 e2 -> Formula (op (as_formula e1, as_formula e2))), t1, t2)
    let bin_predicate op (t1: Expr) t2 =  Bin ((fun e1 e2 -> Formula (op (as_term e1, as_term e2))), t1, t2)
    let bin_op op (t1: Expr) t2 =  Bin ((fun e1 e2 -> Term (op (as_term e1, as_term e2))), t1, t2)
    let unary_bool op (t: Expr) =  Unary ((fun e1 -> Formula (op (as_formula e1))), t)
    let unary_op op (t: Expr) =  Unary ((fun e1 -> Term (op (as_term e1))), t)
    
    match e with
        | ZEquals (t1, t2) -> bin_predicate Equals t1 t2
        | ZLe (t1, t2) -> bin_predicate Le t1 t2
        | ZLt (t1, t2) -> bin_predicate Lt t1 t2
        | ZSLe (t1, t2) -> bin_predicate SLe t1 t2
        | ZSLt (t1, t2) -> bin_predicate SLt t1 t2
        | ZCONJ [| t1 ; t2 |] -> bin_bunch And t1 t2
        | ZDISJ [| t1 ; t2 |] -> bin_bunch Or t1 t2
        | ZDISJ _ | ZCONJ _ -> failwith "Expected exactly two arguments for a Disjunction/Conjunction"
        | ZNot t -> unary_bool Not t
        | ZImplies (l, r) -> bin_bunch Implies l r
        | ZExists (var, t) ->  unary_bool (fun t -> Exists(Var (var.ToString()), t)) t
        | ZTrue -> Const (Formula True)
        | ZFalse -> Const (Formula False)
        | ZVar name -> Const (Term (Var name))
        | ZMult (t1, t2) ->  bin_op Mult t1 t2  
        | ZPlus (t1, t2) -> bin_op Plus t1 t2  
        | ZBVAnd (t1, t2) -> bin_op BitAnd t1 t2  
        | ZBVOr (t1, t2) -> bin_op BitOr t1 t2  
        | ZBVShR (t1, t2) -> bin_op ShiftRightLogical t1 t2 
        | ZBVShL (t1, t2) -> bin_op ShiftLeft t1 t2  
        | ZBV c -> Const (Term (BV c))
        | ZBVZeroEx (t, d) -> unary_op (fun t -> ZeroEx (t, d)) t 
        | ZExtract (t, a, b) -> unary_op (fun t -> Extract (t, a, b)) t
        | t -> sprintf "unexpected z3 expression %O" t |> failwith

let convert_z3 = fold z3_mapper (fun x -> x)


(*let fold_formula eq le lt sle slt conj disj _not implies exists tru fls var mult plus bv_and bv_or bv_shr bv_shl bv_int bv zero_extend extract (expr: Expression)  =
        let rec LoopF (e: Formula) (acc: Formula -> Formula) =  
            
            match e with
                | Equals (t1, t2) -> binary_predicate eq (Term t1) (Term t2)
                | Le (t1, t2) -> binary_predicate le t1 t2
                | Lt (t1, t2) -> binary_predicate lt t1 t2
                | SLe (t1, t2) -> binary_predicate sle t1 t2
                | SLt (t1, t2) -> binary_predicate slt t1 t2
                | And [| t1 ; t2 |] -> binary_list conj t1 t2
                | Or [| t1 ; t2 |] -> binary_list disj t1 t2
                | Not t -> unary_bool_op _not t
                | Implies (l, r) -> binary_bool_op implies l r
                | Exist (var, t) ->  unary_bool_op (exists (Var (var.ToString()))) t
                | True -> Formula tru
                | False -> Formula fls            
                | t ->
                        let descr = t.ToString()
                        failwith "unexpected z3 expression {t}"
        let rec LoopT (e: Term) (acc: Term -> Term) =  
            
            match e with
                | Plus(t1, t2) -> Var ""
                | t ->
                        let descr = t.ToString()
                        failwith "unexpected z3 expression {t}"
        match expr with
         | Formula f -> Formula (LoopF f (fun x -> x))
         | Term t    -> Term    (LoopT t (fun x -> x))
        
*)
let fold_term eq le lt sle slt conj disj _not implies exists tru fls var mult plus bv_and bv_or bv_shr bv_shl bv_int bv zero_extend extract (expr: Term)  =
   Var ""



let tuplify_list2 list =
    match list with
     | [a; b] -> (a, b)
     | _ -> failwith "cannot tuplify list"



let rec formula_from_z3 (expr: BoolExpr) =
    let rec Loop e acc =
            let binary_op_list typ l r = Loop l (fun lacc -> Loop r (fun racc -> acc (typ [lacc; racc])) )
            let binary_op typ l r = Loop l (fun lacc -> Loop r (fun racc -> acc (typ (lacc, racc))) )
            match e with 
            | ZEquals (t1, t2) -> Equals(term_from_z3 t1, term_from_z3 t2)
            | ZLe (t1, t2) -> Le(term_from_z3 t1, term_from_z3 t2)
            | ZLt (t1, t2) -> Lt(term_from_z3 t1, term_from_z3 t2)
            | ZSLe (t1, t2) -> SLe(term_from_z3 t1, term_from_z3 t2)
            | ZSLt (t1, t2) -> SLt(term_from_z3 t1, term_from_z3 t2)
            | ZCONJ [| l ; r |] -> binary_op_list And l r
            | ZDISJ [| l ; r |] -> binary_op_list Or l r
            | ZNot t -> Loop t (fun tacc -> acc (Not tacc))
            | ZImplies (l, r) -> binary_op Implies l r
            | ZExists (var, t) -> Loop t (fun tacc -> acc (Exists (Var (var.ToString()), tacc))) 
            | ZTrue -> acc True
            | ZFalse -> acc False
            | t ->
                failwith "unexpected z3 expression"
    Loop expr (fun x -> x)
//    match expr with 
//            | ZEquals (t1, t2) -> Equals(term_from_z3 t1, term_from_z3 t2)
//            | ZLe (t1, t2) -> Le(term_from_z3 t1, term_from_z3 t2)
//            | ZLt (t1, t2) -> Lt(term_from_z3 t1, term_from_z3 t2)
//            | ZSLe (t1, t2) -> SLe(term_from_z3 t1, term_from_z3 t2)
//            | ZSLt (t1, t2) -> SLt(term_from_z3 t1, term_from_z3 t2)
//            | ZCONJ args ->
//                args |> (Array.map formula_from_z3) |> List.ofArray |> And
//            | ZDISJ args ->
//                args |> (Array.map formula_from_z3) |> List.ofArray |> Or
//            | ZNot t -> Not (formula_from_z3 t)
//            | ZImplies (a, b) -> Implies (formula_from_z3 a, formula_from_z3 b)
//            | ZExists (var, f) -> Exists (Var (var.ToString()), formula_from_z3 f)
//            | ZTrue -> True
//            | ZFalse -> False
//            | t ->
//                failwith "unexpected z3 expression"
            
let rec (|=) (M: IDictionary<string, uint32>) (F: Formula) =
         let interpret_term = interpret_term M
         match F with 
            | And args -> List.forall ((|=) M) args
            | Or args -> List.exists ((|=) M) args
            | True -> true
            | False -> false
            | Equals (t1, t2) -> interpret_term t1 = interpret_term t2
            | Le (t1, t2) ->  interpret_term t1 <= interpret_term t2
            | Lt (t1, t2) ->  interpret_term t1 < interpret_term t2
            | Ge (t1, t2) ->  interpret_term t1 >= interpret_term t2
            | Gt (t1, t2) -> interpret_term t1 > interpret_term t2
            | Not t -> not (M |= t)
            | Implies (t1, t2) -> not (M |= t1) || (M |= t2)
            | Iff (t1, t2) ->  (M |= t1) = (M |= t2) 
            | Exists(name, F) -> failwith "try to check model on quantified formula"
            | _ -> failwith "Unknown formula"
                        

let (|Contains|_|) x (e: Term) =
    if term_contains x e then Some(e) else None

let (|FreeOf|_|) x (e: Term) =
    if not (term_contains x e) then Some(e) else None


let some_matches (|Pattern|_|) expressions =
        List.tryFind (function | Pattern _ -> true | _ -> false) expressions
let each_matches (|Pattern|_|) expressions =
         List.forall (function | Pattern _ -> true | _ -> false) expressions
        
let (|ThisVar|_|) x (e: Term) =
    match e with
    | t when t = x -> Some()
    | _ -> None


let (|+) (|Pattern1|_|) (|Pattern2|_|) =
    let (|UnionPattern|_|) e =
        match e with
            | Pattern1 a | Pattern2 a -> Some(a)
            | _ -> None
    (|UnionPattern|_|)
module BVTProver.FormulaActions

open BVTProver
open Formula
open Z3Patterns
open Microsoft.Z3


type Expression =
    | Formula of Formula
    | Term of Term

let rec interpret_term (M: Map<string, int>) formula: int =
    let interpret_term = interpret_term M

    let d =
        match formula with
        | Var name -> Map.find name M
        | Mult (t1, t2) -> (interpret_term t1) * (interpret_term t2)
        | Plus (t1, t2) -> (interpret_term t1) + (interpret_term t2)
        | Div (t1, d) -> (interpret_term t1) / d
        | Inv t -> -(interpret_term t)
        | Int c -> c

    d %% Term.MaxNumber

let rec substitute_term (M: Map<Term, Term>) term =
    let substitute_term = substitute_term M
    match term with
    | t when Map.containsKey t M -> Map.find t M
    | Mult (t1, t2) -> Mult(substitute_term t1, substitute_term t2)
    | Plus (t1, t2) -> Plus(substitute_term t1, substitute_term t2)
    | Div (t1, d) -> Div(substitute_term t1, d)
    | Inv t -> Inv(substitute_term t)
    | Int t -> Int t
    | Var t -> Var t

let rec substitute_formula (M: Map<Term, Term>) formula: Formula =
         let substitute_formula = substitute_formula M
         let substitute_term = substitute_term M
         match formula with 
            | And args -> And(Array.map substitute_formula args) 
            | Or args -> Or(Array.map substitute_formula args) 
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
            

let rec term_contains (var: Term) term =
    let contains = term_contains var
    match term with
    | t when t = var -> true
    | Mult (t1, t2)
    | Plus (t1, t2) -> contains t1 || contains t2
    | Inv (t)
    | Div (t, _) -> contains t
    | Int _
    | Var _ -> false
    | _ -> failwith "unexpected term"



let rec formula_contains (var: Term) expr =
    let contains = formula_contains var
    let term_contains = term_contains var
    match expr with
    | And args
    | Or args -> Array.exists (fun (f: Formula) -> contains f) args
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


let rec z3fy_term (ctx: Context) (expr: Term): BitVecExpr =
    let z3fy = z3fy_term ctx
    match expr with
    | Var name -> ctx.MkBVConst(name, Term.Bits)
    | Mult (t1, t2) -> ctx.MkBVMul(z3fy t1, z3fy t2)
    | Plus (t1, Inv t2)
    | Plus (Inv t2, t1) -> ctx.MkBVSub(z3fy t1, z3fy t2)
    | Plus (t1, t2) -> ctx.MkBVAdd(z3fy t1, z3fy t2)
    | Div (t1, d) -> ctx.MkBVUDiv(z3fy t1, ctx.MkBV(d, Term.Bits))
    | Inv t -> ctx.MkBVNeg(z3fy t)
    | Int c -> ctx.MkBV(c, Term.Bits) :> BitVecExpr
let rec z3fy_formula (ctx: Context) formula: BoolExpr =
    let z3fy_formula = z3fy_formula ctx
    let z3fy_term = z3fy_term ctx

    let map_z3 args =
        Array.map (fun (f: Formula) -> z3fy_formula f) args

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

let rec term_from_z3 (expr: Expr) =
        match expr with 
            | ZVar name -> Var name
            | ZMult (t1, t2) ->  Mult(term_from_z3 t1, term_from_z3 t2)
            | ZPlus (t1, t2) -> Plus(term_from_z3 t1, term_from_z3 t2)
            | ZInt c -> Int c
            | _ -> failwith "unexpected z3 expression"
let rec formula_from_z3 (expr: Expr) =
        match expr with 
            | ZEquals (t1, t2) -> Equals(term_from_z3 t1, term_from_z3 t2)
            | ZLe (t1, t2) -> Le(term_from_z3 t1, term_from_z3 t2)
            | ZLt (t1, t2) -> Lt(term_from_z3 t1, term_from_z3 t2)
            | ZCONJ args ->  And(Array.map formula_from_z3 args)
            | ZDISJ args ->  Or(Array.map formula_from_z3 args)
            | ZNot t -> Not (formula_from_z3 t)
            | ZImplies (a, b) -> Implies (formula_from_z3 a, formula_from_z3 b)
            | ZExists (var, f) -> Exists (Var (var.ToString()), formula_from_z3 f)
            | _ -> failwith "unexpected z3 expression"
            
let rec (|=) (M: Map<string, int>) (F: Formula) =
         let interpret_term = interpret_term M
         match F with 
            | And args -> Array.forall (fun f -> M |= f) args
            | Or args -> Array.exists (fun f -> M |= f) args
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

let (|ThisVar|_|) x (e: Term) =
    match e with
    | t when t = x -> Some()
    | _ -> None


type Cube (expressions: Formula[]) = // conjunction of literals, without ORs inside
    member this.conjuncts = expressions
    member this.as_formula = And(this.conjuncts)
    
    member this.some_matches (|Pattern|_|) =
        Array.tryFind (fun e -> match e with | Pattern _ -> true | _ -> false) expressions
    member this.each_matches (|Pattern|_|) =
         Array.forall (fun e -> match e with | Pattern _ -> true | _ -> false) expressions

    member this.split (x) =
        let is_free (e: Formula) = not (formula_contains x e)
        let a, b = Array.partition is_free expressions
        Cube a, Cube b
    member this.remove (conjunct) =
        Cube(Array.except [conjunct] this.conjuncts)
    member this.apply_model (M: Map<string, int>) = Array.forall ((|=) M) expressions
         
    static member (+) (a: Cube, b: Cube) =
        [ a.conjuncts ; b.conjuncts ] |> Array.concat |> Cube

let (|+) (|Pattern1|_|) (|Pattern2|_|) =
    let (|UnionPattern|_|) e =
        match e with
            | Pattern1 a | Pattern2 a -> Some(a)
            | _ -> None
    (|UnionPattern|_|)
module BVTProver.Formula

open System
open BVTProver
open Microsoft.Z3
let n = 256
let n2 = 8u

let (%%) a b =
             let c = a % b
             if c < 0 then
                 b + c
             else
                 c
type Term =
    | Int of int
    | Var of string
    | Mult of Term*Term
    | Plus of Term*Term
    | Inv of Term
    | Div of Term*int

    override this.ToString() =
        match this with 
            | Var name -> sprintf "%s" name
            | Mult (t1, t2) -> sprintf "%O*%O" t1 t2
            | Plus (t1, Inv t2) -> sprintf "%O-%O" t1 t2
            | Plus (t1, t2) -> sprintf "%O+%O" t1 t2
            | Inv t -> sprintf "-(%O)" t
            | Div (t1, n) -> sprintf "%O div %d" t1 n
            | Int n -> sprintf "%d" n
            | _ -> failwith "unknown term"
    
    member this.interpret (M: Map<string, int>) : int =

         match this with 
            | Var name -> M.Item(name) %% n
            | Mult (t1, t2) -> ((t1.interpret M) * (t2.interpret M)) %% n
            | Plus (t1, t2) -> ((t1.interpret M) + (t2.interpret M)) %% n
            | Div (t1, d) -> ((t1.interpret M) / d) %% n
            | Inv t -> (-(t.interpret M)) %% n
            | Int c -> c %% n
    member this.substitute (M: Map<Term, Term>) =
         match this with
            | t when M.ContainsKey(t) -> M.[t]
            | Mult (t1, t2) -> Mult(t1.substitute M, t2.substitute M)
            | Plus (t1, t2) -> Plus (t1.substitute M, t2.substitute M)
            | Div (t1, d) -> Div(t1.substitute M, d)
            | Inv t -> Inv(t.substitute M)
            | t -> t
    member this.contains (var: Term) =
            match this with
                | t when t=var -> true
                | Mult (t1, t2)
                | Plus (t1, t2) -> t1.contains var || t2.contains var
                | Inv (t)
                | Div (t, _) -> t.contains var
                | (Int _) -> false
                | Var _ -> false
                | _ -> failwith "unexpected term"
    member this.z3 (ctx: Context): BitVecExpr =
        match this with 
            | Var name -> ctx.MkBVConst(name, n2)
            | Mult (t1, t2) ->  ctx.MkBVMul(t1.z3 ctx, t2.z3 ctx)
            | Plus (t1, Inv t2)
            | Plus (Inv t2, t1) -> ctx.MkBVSub(t1.z3 ctx, t2.z3 ctx)
            | Plus (t1, t2) -> ctx.MkBVAdd(t1.z3 ctx, t2.z3 ctx)
            | Div (t1, d) -> ctx.MkBVUDiv(t1.z3 ctx, ctx.MkBV(d, n2))
            | Inv t -> ctx.MkBVNeg(t.z3 ctx) 
            | Int c -> ctx.MkBV(c, n2) :> BitVecExpr
type Formula =
    | And of Formula[]
    | Or of Formula[]
    | Iff of Formula*Formula
    | Implies of Formula*Formula
    | Not of Formula
    | Exists of (Term*Formula)
    | Le of Term*Term
    | Lt of Term*Term
    | Ge of Term*Term // see AsLe, AsLt active patterns for unambiguous matching
    | Gt of Term*Term
    | Equals of Term*Term
    | True
    | False
    
    override this.ToString() =
        let join args = String.Join(',', (Array.map string args))
        match this with 
            | And args -> sprintf "And(%s)" (join args)
            | Or args -> sprintf "Or(%s)" (join args)
            | True -> "True"
            | False -> "False"
            | Exists(name, F) -> sprintf "Exists(%O, %O)" name F 
            | Equals (t1, t2) -> sprintf "%O=%O" t1 t2
            | Le (t1, t2) ->  sprintf "%O<=%O" t1 t2
            | Lt (t1, t2) ->  sprintf "%O<%O" t1 t2
            | Ge (t1, t2) ->  sprintf "%O>=%O" t1 t2
            | Gt (t1, t2) ->  sprintf "%O>%O" t1 t2
            | Not t -> sprintf "Not(%O)" t
            | Implies (t1, t2) -> sprintf "%O => %O" t1 t2
            | Iff (t1, t2) -> sprintf "%O <=> %O" t1 t2
            
    static member check (M: Map<string, int>)  (F: Formula) = M |= F
    static member (|=) (M: Map<string, int>, F: Formula) =
         match F with 
            | And args -> Array.forall (fun f -> M |= f) args
            | Or args -> Array.exists (fun f -> M |= f) args
            | True -> true
            | False -> false
            | Equals (t1, t2) -> (t1.interpret M) = (t2.interpret M)
            | Le (t1, t2) ->  let ok = (t1.interpret M) <= (t2.interpret M)
                              ok
            | Lt (t1, t2) ->  (t1.interpret M) < (t2.interpret M)
            | Ge (t1, t2) ->  (t1.interpret M) >= (t2.interpret M)
            | Gt (t1, t2) -> (t1.interpret M) > (t2.interpret M)
            | Not t -> not (M |= t)
            | Implies (t1, t2) -> not (M |= t1) || (M |= t2)
            | Iff (t1, t2) ->  (M |= t1) = (M |= t2) 
            | Exists(name, F) -> failwith "try to check model on quantified formula"
            | _ -> failwith "Unknown formula"
            
    member this.substitute (M: Map<Term, Term>): Formula =
         let subst_all (e: Formula) = e.substitute M
         match this with 
            | And args -> And(Array.map subst_all args) 
            | Or args -> Or(Array.map subst_all args) 
            | Equals (t1, t2) -> Equals(t1.substitute M, t2.substitute M) 
            | Le (t1, t2) ->  Le(t1.substitute M, t2.substitute M) 
            | Lt (t1, t2) ->  Lt(t1.substitute M, t2.substitute M) 
            | Ge (t1, t2) ->  Ge(t1.substitute M, t2.substitute M) 
            | Gt (t1, t2) -> Gt(t1.substitute M, t2.substitute M) 
            | Not t -> Not (t.substitute M)
            | Implies (t1, t2) -> Implies(t1.substitute M, t2.substitute M) 
            | Iff (t1, t2) ->  Iff (t1.substitute M, t2.substitute M) 
            | Exists(name, F) -> failwith "try to substitute terms on quantified formula"
            | (True | False) as constant -> constant 
            



    static member (~-) (t: Formula) = Not(t)
    static member (=>) (t1: Formula, t2: Formula) = Implies(t1, t2)


    
    member this.contains (var: Term) =
            match this with
                | And args
                | Or args -> Array.exists (fun (f: Formula) -> f.contains var) args
                | Equals (t1, t2)
                | Le (t1, t2)
                | Lt (t1, t2) 
                | Ge (t1, t2)
                | Gt (t1, t2) -> t1.contains var || t2.contains var
                | Implies (t1, t2)
                | Iff (t1, t2) -> t1.contains var || t2.contains var
                | Exists(_, t)
                | Not t -> t.contains var
                | _ -> false
                
    member this.z3 (ctx: Context): BoolExpr =
        let map_z3 args = Array.map (fun (f: Formula) -> f.z3 ctx) args
        match this with
                | And args -> ctx.MkAnd(map_z3 args)
                | Or args -> ctx.MkOr(map_z3 args)
                | Equals (t1, t2) -> ctx.MkEq(t1.z3 ctx, t2.z3 ctx)
                | Le (t1, t2) -> ctx.MkBVULE(t1.z3 ctx, t2.z3 ctx)
                | Lt (t1, t2) -> ctx.MkBVULT(t1.z3 ctx, t2.z3 ctx)
                | Ge (t1, t2) -> ctx.MkBVUGE(t1.z3 ctx, t2.z3 ctx)
                | Gt (t1, t2) -> ctx.MkBVUGT(t1.z3 ctx, t2.z3 ctx)
                | Implies (t1, t2) -> ctx.MkImplies(t1.z3 ctx, t2.z3 ctx)
                | Iff (t1, t2) -> ctx.MkIff(t1.z3 ctx, t2.z3 ctx)
                | Exists (t, t2) -> ctx.MkExists([| t.z3 ctx |], t2.z3 ctx) :> BoolExpr
                | Not t -> ctx.MkNot(t.z3 ctx)
                | False -> ctx.MkFalse()
                | True -> ctx.MkTrue()
                | _ -> failwith "unexpected formula"
type Term with
    static member Zero = Int 0 
    static member One = Int 1 
    static member Max = Int (n-1) 
    member this.SmartInv =
        match this with
            | Inv t -> t
            | t -> Inv t
    static member (-) (t1: Term, t2: Term) =
        match t1 with
            | Int 0 -> t2.SmartInv
            | _ -> Plus(t1, t2.SmartInv)
    static member (+) (t1: Term, t2: Term) =
        match t1, t2 with
            | Int 0, t
            | t, Int 0 -> t
            | t1, t2 -> Plus(t1, t2)
//    static member (/) (t1: Term, t2: Term) = Div(t1, t2)
    
    static member (*) (t1: Term, t2: Term) = Mult(t1, t2)
    static member (*) (t1: int, t2: Term) = Mult(Int t1, t2)
    static member (===) (t1: Term, t2: Term) = Equals(t1, t2)
    static member (<==) (t1: Term, t2: Term) = Le(t1, t2)
    static member (>==) (t1: Term, t2: Term) = Ge(t1, t2)
    static member (>!) (t1: Term, t2: Term) = Gt(t1, t2)
    static member (<!) (t1: Term, t2: Term) = Lt(t1, t2)
    
let (|AsMult|_|) (e: Term) =
     match e with
     | Mult (a, b) -> Some (a, b)
     | a -> Some(Int 1, a)

let (|AsLe|_|) (e: Formula) =
     match e with
        | Le(t1, t2) 
        | Ge(t2, t1) -> Some(t1, t2)
//        | Lt(t1, t2)
//        | Gt(t2, t1) -> Some(t1+(Int 1), t2) // overflow possible
        | _ -> None


let (|AsLt|_|) (e: Formula) =
     match e with
        | Lt(t1, t2) 
        | Gt(t2, t1) -> Some(t1, t2)
        | _ -> None

type Cube (expressions: Formula[]) = // conjunction of literals, without ORs inside
    member this.conjuncts = expressions
    member this.as_formula = And(this.conjuncts)
    
    member this.some_matches (|Pattern|_|) =
        Array.tryFind (fun e -> match e with | Pattern _ -> true | _ -> false) expressions
    member this.each_matches (|Pattern|_|) =
         Array.forall (fun e -> match e with | Pattern _ -> true | _ -> false) expressions

    member this.split (x) =
        let is_free (e: Formula) = not (e.contains x)
        let (a, b) = Array.partition is_free expressions
        Cube a, Cube b
    member this.remove (conjunct) =
        Cube(Array.except [conjunct] this.conjuncts)
    member this.apply_model (M: Map<string, int>) = Array.forall (Formula.check M) expressions
         
    static member (+) (a: Cube, b: Cube) =
        [ a.conjuncts ; b.conjuncts ] |> Array.concat |> Cube
let (|Contains|_|) x (e: Term) = if e.contains x then Some(e) else None
let (|FreeOf|_|) x (e: Term) = if not(e.contains x) then Some(e) else None
    
let (|ThisVar|_|) x (e: Term) =
            match e with
                | t when t=x -> Some()
                | _ -> None
let (|+) (|Pattern1|_|) (|Pattern2|_|) =
    let (|UnionPattern|_|) e =
        match e with
            | Pattern1 a | Pattern2 a -> Some(a)
            | _ -> None
    (|UnionPattern|_|)
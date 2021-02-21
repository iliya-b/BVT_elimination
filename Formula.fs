module BVTProver.Formula

open System
open Microsoft.Z3
type Term =
    | Int of int
    | Var of string
    | Mult of Term*Term
    | Plus of Term*Term
    | Minus of Term*Term
    | Div of Term*int
    override this.ToString() =
        match this with 
            | Var name -> sprintf "$%s" name
            | Mult (t1, t2) -> sprintf "%O*%O" t1 t2
            | Plus (t1, t2) -> sprintf "%O+%O" t1 t2
            | Minus (t1, t2) -> sprintf "%O-%O" t1 t2
            | Div (t1, n) -> sprintf "%O div %d" t1 n
    
type Formula =
    | And of Formula[]
    | Or of Formula[]
    | Implies of Formula*Formula
    | Not of Formula
    | Exists of (Term*Formula)
    | Le of Term*Term
    | Lt of Term*Term
    | Ge of Term*Term
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
     member this.CHECK_MODEL (M: Map<Expr, Expr>) (F: BoolExpr) =
            let s = (M |> Map.toArray |> Array.unzip |> F.Substitute ).Simplify()
            s.IsTrue
    
    static member (~-) (t: Formula) = Not(t)
    static member (-) (t1: Term, t2: Term) =
        match t1 with  // a-b === a + (0-b)
           | Int 0 -> Minus(t1, t2)
           | t1 -> Plus(t1, Minus(Int 0, t2))
    static member (+) (t1: Term, t2: Term) =
        match t1, t2 with
            | Int 0, t
            | t, Int 0 -> t
            | t1, t2 -> Plus(t1, t2)
    static member (==) (t1: Term, t2: Term) = Equals(t1, t2)
    static member (<=) (t1: Term, t2: Term) = Le(t1, t2)
    static member (>=) (t1: Term, t2: Term) = Ge(t1, t2)
    static member (>) (t1: Term, t2: Term) = Gt(t1, t2)
    static member (<) (t1: Term, t2: Term) = Lt(t1, t2)

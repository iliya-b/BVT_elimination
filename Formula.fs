module BVTProver.Formula
open System


let (%%) a b = // python-like mod
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
    | Div of Term*Term
    | Extract of Term*int*int

    override this.ToString() =
        match this with 
            | Var name -> sprintf "%s" name
            | Mult (t1, t2) -> sprintf "%O*%O" t1 t2
            | Plus (t1, Inv t2) -> sprintf "(%O-%O)" t1 t2
            | Plus (t1, t2) -> sprintf "(%O+%O)" t1 t2
            | Inv t -> sprintf "-(%O)" t
            | Div (t1, Int n) -> sprintf "(%O div %d)" t1 n
            | Int n -> sprintf "%d" n
            | Extract(t, a, b) -> sprintf "(%O)[%d..%d]" t a b
            | _ -> failwith "unknown term"
    
type Formula =
    | And of Formula list
    | Or of Formula list
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
        let join args = String.Join(',', (List.map string args))
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


    static member (~-) (t: Formula) = Not(t)
    static member (=>) (t1: Formula, t2: Formula) = Implies(t1, t2)

                

type Term with
    static member Zero = Int 0 
    static member One = Int 1 
    static member Max = Int 255
    static member MaxNumber = 255
    static member Bits = 8u
    member private this.SmartInv =
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


module BVTProver.Formula
open System
open System.Collections


let (%%) a b = // python-like mod
    let c = a % b
    if c < 0u then
        b + c
    else
        c
        
type Term =
    | BV of BitArray // todo: use BitArray
    | Var of string
    | Mult of Term*Term
    | Plus of Term*Term
    | Inv of Term
    | Div of Term*Term
    | Extract of Term*int*int
    | BitAnd of Term*Term
    | BitOr of Term*Term
    | ShiftLeft of Term*Term
    | ShiftRightLogical of Term*Term
    | ZeroEx of Term*int

    
let private MaxInt = uint32 Int32.MaxValue
let Int (N: uint32) = 
    if N > MaxInt then
        failwith "Supporting only 0 <= x <= Int32.MaxValue"
    else
        BV (BitArray (BitConverter.GetBytes(N)))
let (|Int|_|) x =
    match x with
     | BV x ->  let res = Array.create<int> 1 0 
                x.CopyTo(res, 0)       // maximum integer is Int32.MaxValue, not UInt32
                Some (uint32 res.[0])  // problem is that BitArray supports converting only to int32
     | _ -> None
type Formula =
    | And of Formula list
    | Or of Formula list
    | Iff of Formula*Formula
    | Implies of Formula*Formula
    | Not of Formula
    | Exists of (Term*Formula)
    | Le of Term*Term
    | SLe of Term*Term
    | Lt of Term*Term
    | SLt of Term*Term
    
    | Ge of Term*Term // eliminate Ge/Gt
    | SGe of Term*Term 
    | Gt of Term*Term
    | SGt of Term*Term
    
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


    static member (~-) t = Not(t)
    static member (=>) (t1, t2) = Implies(t1, t2)

                

type Term with
    static member Zero = Int 0u
    static member One = Int 1u
    static member Max = Int 255u
    static member MaxNumber = 255u
    static member Bits = 8u
    member private this.SmartInv =
        match this with
            | Inv t -> t
            | t -> Inv t
    static member (-) (t1: Term, t2: Term) =
        match t1 with
            | Int 0u -> t2.SmartInv
            | _ -> Plus(t1, t2.SmartInv)
    static member (+) (t1: Term, t2: Term) =
        match t1, t2 with
            | Int 0u, t
            | t, Int 0u -> t
            | t1, t2 -> Plus(t1, t2)
//    static member (/) (t1: Term, t2: Term) = Div(t1, t2)
    
    static member (*) (t1, t2)  = Mult(t1, t2)
    static member (*) (t1, t2)  = Mult(Int t1, t2)
    static member (===) (t1, t2)  = Equals(t1, t2)
    static member (<==) (t1, t2)  = Le(t1, t2)
    static member (>==) (t1, t2)  = Ge(t1, t2)
    static member (>!) (t1, t2)  = Gt(t1, t2)
    static member (<!) (t1, t2)  = Lt(t1, t2)

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
    
let (|AsMult|_|) e =
     match e with
     | Mult (a, b) -> Some (a, b)
     | a -> Some(Int 1u, a)

let (|AsLe|_|) e =
     match e with
        | Le(t1, t2) 
        | Ge(t2, t1) -> Some(t1, t2)
//        | Lt(t1, t2)
//        | Gt(t2, t1) -> Some(t1+(Int 1), t2) // overflow possible
        | _ -> None


let (|AsLt|_|) e =
     match e with
        | Lt(t1, t2) 
        | Gt(t2, t1) -> Some(t1, t2)
        | _ -> None


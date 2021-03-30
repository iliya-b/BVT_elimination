module BVTProver.Formula
open System
open Helpers

let private MaxInt = uint32 Int32.MaxValue

type IntVector = uint32*uint32 // value*bit_len
type VarVector = string*uint32

type Term =
    | Integer of IntVector
    | Var of VarVector
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
    | Ite of Formula*Term*Term

and Formula =
    | And of Formula list
    | Or of Formula list
    | Iff of Formula*Formula
    | Implies of Formula*Formula
    | Not of Formula
    | Exists of Term*Formula
    | Le of Term*Term
    | SLe of Term*Term
    | Lt of Term*Term
    | SLt of Term*Term
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
            | Not t -> sprintf "Not(%O)" t
            | Implies (t1, t2) -> sprintf "%O => %O" t1 t2
            | Iff (t1, t2) -> sprintf "%O <=> %O" t1 t2
            | _ -> unexpected ()


    static member (~-) t = Not t
    static member (=>) (t1, t2) = Implies (t1, t2)
    static member (<=>) (t1, t2) = Iff (t1, t2)

let Int bit_len N = 
    if N > MaxInt then
        failwith "Supporting only 0 <= x <= Int32.MaxValue"
    else
        Integer (N, bit_len)
        
let (|Int|_|) x =
    match x with
     | Integer (x, _) -> Some x
     | _ -> None
type Term with
    static member ZeroM = Int 0u
    static member OneM = Int 1u

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

    static member (*) (t1, t2)  = Mult(t1, t2)

    static member (===) (t1, t2)  = Equals(t1, t2)
    static member (<==) (t1, t2)  = Le(t1, t2)
    static member (>==) (t1, t2)  = Le(t2, t1)
    static member (>!) (t1, t2)  = Lt(t2, t1)
    static member (<!) (t1, t2)  = Lt(t1, t2)

    override this.ToString() =
        match this with 
            | Var (name, size) -> sprintf "%s" name
            | Mult (t1, t2) -> sprintf "%O*%O" t1 t2
            | Plus (t1, Inv t2) -> sprintf "(%O-%O)" t1 t2
            | Plus (t1, t2) -> sprintf "(%O+%O)" t1 t2
            | Inv t -> sprintf "-(%O)" t
            | Div (t1, Int n) -> sprintf "(%O div %d)" t1 n
            | Int n -> sprintf "%d" n
            | Extract(t, a, b) -> sprintf "(%O)[%d..%d]" t a b
            | Ite (f, a, b) -> sprintf "if (%O) then (%O) else (%O)" f a b
            | _ -> failwith "unknown term"
    

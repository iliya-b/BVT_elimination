module BVTProver.Formula
open System
open Helpers
open MathHelpers
open Microsoft.Z3

let private MaxInt = uint32 UInt32.MaxValue

type IntVector = uint32*uint32 // value*bit_len
type VarVector = string*uint32

type Term =
    | Integer of IntVector
    | Var of VarVector
    | Mult of Term*Term
    | Plus of Term*Term
    | Inv of Term
    | Div of Term*Term
    | SDiv of Term*Term
    
    | SRem of Term*Term
    | Rem of Term*Term
    | SMod of Term*Term
    
    | Extract of Term*int*int
    | Concat of Term*Term
    | BitAnd of Term*Term
    | BitOr of Term*Term
    | BitXor of Term*Term
    | BitNot of Term
    | ShiftLeft of Term*Term
    | ShiftRightLogical of Term*Term
    | ZeroEx of Term*int
    | Ite of Formula*Term*Term


and Formula =
    | And of Formula list
    | Or of Formula list
    | Xor of Formula list
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
            | Xor args -> sprintf "Xor(%s)" (join args)
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
    if N > (pown_2 bit_len - 1UL |> uint32) || N < 0u then
        failwith "Overflow"
    elif bit_len=0u then
        failwith "zero bitlen"
    else
        Integer (N, bit_len)
        
let (|Int|_|) x =
    match x with
     | Integer (x, _) -> Some x
     | _ -> None
type Term with
    static member ZeroM bits = Int bits 0u
    static member OneM bits = Int bits 1u

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
            | Var (name, _) -> sprintf "%s" name
            | Mult (t1, t2) -> sprintf "(%O*%O)" t1 t2
            | ZeroEx (t, d) -> sprintf " ex(%O, %d) " t d
            | ShiftLeft (t1, t2) -> sprintf "(%O<<<%O)" t1 t2
            | ShiftRightLogical (t1, t2) -> sprintf "(%O>>>%O)" t1 t2
            | BitAnd (t1, t2) -> sprintf "(%O&&&%O)" t1 t2
            | BitOr (t1, t2) -> sprintf "(%O|||%O)" t1 t2
            | BitXor (t1, t2) -> sprintf "(%O^^^%O)" t1 t2
            | BitNot t -> sprintf "~(%O)" t
            | Plus (t1, Inv t2) -> sprintf "(%O-%O)" t1 t2
            | Plus (t1, t2) -> sprintf "(%O+%O)" t1 t2
            | Inv t -> sprintf "-(%O)" t
            | Div (t1, t2) -> sprintf "(%O div %O)" t1 t2
            | SDiv (t1, t2) -> sprintf "(%O sdiv %O)" t1 t2
            | Integer (n, _) -> sprintf "%d" n
            | Extract(t, a, b) -> sprintf "(%O)[%d..%d]" t a b
            | Concat(t1, t2) -> sprintf "(%O ^ %O)" t1 t2
            | Ite (f, a, b) -> sprintf "if (%O) then (%O) else (%O)" f a b
            | Rem (t1, t2) -> sprintf "(%O urem %O)" t1 t2
            | SRem (t1, t2) -> sprintf "(%O srem %O)" t1 t2
            | SMod (t1, t2) -> sprintf "(%O smod %O)" t1 t2


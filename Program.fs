module Program
open System
open System.Collections
open System.Numerics
open BVTProver
open BVTProver.Formula
open BVTProver.FormulaActions
open MathHelpers

open Continuations
open Microsoft.Z3
open Z3Patterns

type private RecursiveBuilder() =
        member this.Bind(x, f) = f x
        member this.Return(x) = x
        member this.ReturnFrom(x) = x
//type DelegateBinaryOp = delegate of (Rec*Rec -> Rec) * Rec * Rec -> Rec

[<EntryPoint>]
let main argv =
    (* Example:
        Your formula: Exists(x, And(Exists(y, Or(x==y, x==a)), And(x==a, x==b)))
        Free formula: a==b
    *)
    
    let test =  Mult (Int 3u, Plus (Plus (Plus (Plus (Plus (Plus (Int 4u, Int 9u), Int 9u), Int 9u), Int 9u), Int 9u), Int 9u))
    
    
    let id x = x
    

    let ctx = new Context()
    let expr = ctx.MkBVMul(ctx.MkBVAdd(ctx.MkBV(10, 8u), ctx.MkBVConst("x", 8u)), ctx.MkBV(3, 8u))
    let k = fold convert_z3 (fun x -> x) (expr :> Expr)
    0
   (*
   
         | Bin(Op, x, y) -> fold (binary_predicate (bin_f Op) fold acc x) y
         | Unary (Op, x) -> fold (unary_op (un_f Op) fold acc) x
         | Const (Int t) -> Const (Int (t+1u))
         *)
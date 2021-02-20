module BVTProver.Mbp
//open BVTProver
open BvtPatterns
open Microsoft.Z3

let ctx = new Context()
let MbpZ (f: Expr) var (M: Map<Expr, Expr>)  =
    match f with
        | LIA_1 var (free, _) -> ctx.MkAnd(free) :> Expr // ????
        | _ -> (M |> Map.toArray |> Array.unzip |> f.Substitute).Simplify()
        
//let LazyMbp (f: Expr) var (M: Map<Expr, Expr>) =
    
    

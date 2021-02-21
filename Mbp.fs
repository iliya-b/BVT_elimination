module BVTProver.Mbp
//open BVTProver
open System
open BVTProver.Bvt
open BvtPatterns
open Microsoft.Z3
let rec gcd (a:int, b:int) =
    match b with
       | x when x = 0 -> a
       | _ -> gcd (b, a % b)

// least common divisor
let rec lcm (a:int, b:int) =
    (a * b) / gcd (a,b)

// least common divisor for a list of numbers
let rec lcmlist (list: int list) =
    match list with
        | [] -> 1
        | [a] ->  a
        | [a;b] ->  lcm(a,b)
        | h::t  ->  lcm(h, lcmlist t)
     
let (|+) (|Pattern1|_|) (|Pattern2|_|) =
    let (|UnionPattern|_|) e =
        match e with
            | Pattern1 a | Pattern2 a -> Some(a)
            | _ -> None
    (|UnionPattern|_|)
    
let ctx = new Context()
let bvt = BVT(ctx, n, nn)

let bv_int (num:int) = ctx.MkBV(num, n)

type Cube (expressions: BoolExpr[]) =
    member this.conjuncts = expressions
    member this.each_matches (|Pattern|_|) =
         Array.forall (fun e -> match e with | Pattern _ -> true | _ -> false) expressions

    member this.split (bounded_variable) =
        let is_free e = not (contains e bounded_variable)
        let (a, b) = Array.partition is_free expressions
        Cube(a), Cube(b)
        
    member this.apply_model (M: Map<Expr, Expr>) =
         let apply_model (M: Map<Expr, Expr>) (F: BoolExpr) =
            (M |> Map.toArray |> Array.unzip |> F.Substitute ).Simplify() :?> BoolExpr
         (Array.map (apply_model M) expressions) |> Cube
         
    static member (+) (a: Cube, b: Cube) =
        [ a.conjuncts ; b.conjuncts ] |> Array.concat |> Cube
        
            
        
type LazyMbp () =

        
    member this.MbpZ (cube: Cube) (bounded_variable: Expr) (M: Map<Expr, Expr>)  =
        let (|ThisVar|_|) (expr: Expr) =
            match expr with
                | Var x when x=expr.FuncDecl.Name.ToString() -> Some()
                | _ -> None

        let (|ConstMultiplication|_|) (expr: BitVecExpr) : int option = 
                match expr with
                    | Mult (Int t, ThisVar)
                    | Mult (ThisVar, Int t) -> Some(t)
                    | ThisVar _ as t -> Some(1)
                    | _ -> None
                    
        let (|UpperBound|_|) (conjunct: Expr) : (int*BitVecExpr) option =  // such that num*x <= term
                match conjunct with
                    | Le(ConstMultiplication t1, t2) when not (contains t2 bounded_variable) -> Some(t1, t2)
                    | Lt(ConstMultiplication t1, t2) when not (contains t2 bounded_variable) -> Some(t1+1, t2)
                    | _ -> None
        let (|LowerBound|_|) (conjunct: Expr) : (int*BitVecExpr) option =   // such that term < num*x
                match conjunct with
                    | Lt (t1, ConstMultiplication t2) when not (contains t1 bounded_variable) -> Some(t2, t1)
                    | Le (t1, ConstMultiplication t2) when not (contains t1 bounded_variable) -> Some(t2+1, t1)
                    | _ -> None
        let (|AnyBound|_|) = (|UpperBound|_|) |+ (|LowerBound|_|)

         
        let (|TautologicalInequality|_|) (conjunct: Expr) =
                match conjunct with
                    | Le(ConstMultiplication t1, t2) -> Some(t1, t2)
                    | _ -> None
                           
        let (|Rule1|_|) (cube: Cube) =
            if cube.each_matches (|TautologicalInequality|_|) then
                Some(cube)
            else
                None
        let coeffs e = Array.map (fun e -> match e with | AnyBound (num, _) -> num | _ -> failwith "unexpected") e
            
            
        let check_model model lcm e =
            match e with
             | AnyBound (num, t) -> bvt.CHECK_MODEL model (ctx.MkBVULE( t, ctx.MkBVUDiv( (bv_int -1), ctx.MkBVUDiv((bv_int lcm), (bv_int num)) )))
             | _ -> failwith "unexpected literal" 
            
            
                            
        let (|Rule2|_|) (cube: Cube) =
            
            if cube.each_matches (|AnyBound|_|) then
                let LCM = cube.conjuncts |> coeffs |> Array.toList |> lcmlist
                let var_value = match M.Item(bounded_variable) with
                                   | Int x -> x
                                   | _ -> failwith "bounded variable is not a variable"
                // side conditions
                let lcm_overflows = LCM >= pown 2 nn
                let lcm_multiplied_overflows = var_value*LCM >= pown 2 nn
                let model_satisfies = Array.forall (check_model M LCM) cube.conjuncts
                
                if not lcm_overflows && not lcm_multiplied_overflows && model_satisfies then
                    Some(cube)
                else None
            else None

                
        let (open_conjuncts, residual) = cube.split bounded_variable

        let residual: Cube =
            match residual with
              | Rule1 _ -> residual
              | Rule2 _ ->
                let LCM = cube.conjuncts |> coeffs |> Array.toList |> lcmlist
                let lcm = bv_int LCM
                let make_conjunct1 i conjunct =
                    match conjunct with
                       | AnyBound (num, t) -> ctx.MkBVULE(t, ctx.MkBVUDiv((bv_int -1), ctx.MkBVUDiv(lcm, (bv_int num))))
                       | _ -> failwith "unexpected term"
                let lower_term=ctx.MkBV(1, n)
                let numL=1
                let U=1
                let L=1
                let upper_term=ctx.MkBV(1, n)
                let numU=1
                let make_conjunct2 i conjunct =
                    match conjunct with
                       | _ when i=L || i=U -> ctx.MkTrue()
                       | UpperBound (num, t) -> ctx.MkBVULE(ctx.MkBVMul(t, ctx.MkBVUDiv(lcm, (bv_int num))), ctx.MkBVMul(lower_term, ctx.MkBVUDiv(lcm, (bv_int numL))))
                       | LowerBound (num, t) -> ctx.MkBVULE(ctx.MkBVMul(upper_term, ctx.MkBVUDiv(lcm, (bv_int numU))), ctx.MkBVMul(t, ctx.MkBVUDiv(lcm, (bv_int num))))
                       | _ -> failwith "unexpected term"
                let c1 = residual.conjuncts |> (Array.mapi make_conjunct1) |> Cube
                let c2 = residual.conjuncts |> (Array.mapi make_conjunct2) |> Cube
                c1 + c2 + Cube([| ctx.MkBVULT(ctx.MkBVMul(lower_term, ctx.MkBVMul(lcm, (bv_int numL))), ctx.MkBVMul(upper_term, ctx.MkBVMul(lcm, (bv_int numU)))) |])
                                   
              | cube -> cube.apply_model M
        open_conjuncts + residual 
                           

//let LazyMbp (f: Expr) var (M: Map<Expr, Expr>) =
    
    

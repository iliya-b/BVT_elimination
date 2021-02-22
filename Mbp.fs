module BVTProver.Mbp
//open BVTProver
open System
open BVTProver.Bvt
open Formula
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
let bvt = BVT(ctx, 8u, 8)


type Cube (expressions: Formula[]) =
    member this.conjuncts = expressions
    member this.each_matches (|Pattern|_|) =
         Array.forall (fun e -> match e with | Pattern _ -> true | _ -> false) expressions

    member this.split (bounded_variable) =
        let is_free (e: Formula) = not (e.contains (Var bounded_variable))
        let (a, b) = Array.partition is_free expressions
        Cube(a), Cube(b)
        
    member this.apply_model (M: Map<string, int>) = Array.forall (Formula.check M) expressions
         
    static member (+) (a: Cube, b: Cube) =
        [ a.conjuncts ; b.conjuncts ] |> Array.concat |> Cube
        
            
        
type LazyMbp () =

        
    member this.MbpZ (cube: Cube) (bounded_variable: string) (M: Map<string, int>)  =
        let (|ThisVar|_|) (expr: Term) =
            match expr with
                | Var x when x=bounded_variable -> Some()
                | _ -> None

        let (|ConstMultiplication|_|) (expr: Term) : int option = 
                match expr with
                    | Mult (Int t, ThisVar)
                    | Mult (ThisVar, Int t) -> Some(t)
                    | ThisVar _ as t -> Some(1)
                    | _ -> None
                    
        let (|UpperBound|_|) (conjunct: Formula) : (int*Term) option =  // such that num*x <= term
                match conjunct with
                    | Le(ConstMultiplication t1, t2) when not (t2.contains (Var bounded_variable)) -> Some(t1, t2)
                    | Lt(ConstMultiplication t1, t2) when not (t2.contains (Var bounded_variable)) -> Some(t1+1, t2)
                    | _ -> None
        let (|LowerBound|_|) (conjunct: Formula) : (int*Term) option =   // such that term < num*x
                match conjunct with
                    | Lt (t1, ConstMultiplication t2) when not (t1.contains (Var bounded_variable)) -> Some(t2, t1)
                    | Le (t1, ConstMultiplication t2) when not (t1.contains (Var bounded_variable)) -> Some(t2+1, t1)
                    | _ -> None
        let (|AnyBound|_|) = (|UpperBound|_|) |+ (|LowerBound|_|)

         
        let (|TautologicalInequality|_|) (conjunct: Formula) =
                match conjunct with
                    | Le(ConstMultiplication t1, t2) -> Some(t1, t2)
                    | _ -> None
                           
        let (|Rule1|_|) (cube: Cube) =
            if cube.each_matches (|TautologicalInequality|_|) then
                Some(cube)
            else
                None

        let coeffs e = match e with
                          | UpperBound(num, t) -> (true, (num, t))
                          | LowerBound(num, t) -> (false, (num, t))
                          | _ -> failwith "?"
            
        let check_model model (lcm: int) e =
            match e with
             | AnyBound (num, t) ->  model |=  (t <== Int ((n-1)/(lcm/num)))
             | _ -> failwith "unexpected literal" 
            
            
                            
        let (|Rule2|_|) (cube: Cube) =
            // todo: lazy computation
            if cube.each_matches (|AnyBound|_|) then
                let LCM = cube.conjuncts |>
                          (Array.map coeffs) |>
                          (Array.map snd) |>
                          (Array.map fst) |>
                          Array.toList |>
                          lcmlist
                          
                let var_value = M.Item(bounded_variable)
                // side conditions
                let lcm_overflows = LCM >= n
                let lcm_multiplied_overflows = var_value*LCM >= n
                let model_satisfies = Array.forall (check_model M LCM) cube.conjuncts
                
                if not lcm_overflows && not lcm_multiplied_overflows && model_satisfies then
                    let data = Array.map coeffs cube.conjuncts
                    let a, b = data |> (Array.partition fst) 
                    let a_coeffs, a_bounds = a |> (Array.map snd) |> Array.unzip
                    let b_coeffs, b_bounds = b |> (Array.map snd) |> Array.unzip
                    Some(LCM, a_coeffs, a_bounds, b_coeffs, b_bounds)
                else None
            else None

                
        let (open_conjuncts, residual) = cube.split bounded_variable

        let residual: Cube =
            match residual with
              | Rule1 _ -> residual
              | Rule2 (lcm, u_coeffs, upper_bounds, l_coeffs, lower_bounds) ->
                
                let exact_bound a b = (a, b)
                                        ||> Array.map2 (fun n (t: Term) -> (t.interpret M)*(lcm/n))
                                        |> Array.indexed
                                        |> Array.maxBy snd
                                        |> fst
                                
                let U = exact_bound u_coeffs upper_bounds
                let L = exact_bound l_coeffs lower_bounds 
                let coefficient_L = Array.get l_coeffs L
                let coefficient_U = Array.get u_coeffs U
                let term_L = Array.get lower_bounds L
                let term_U = Array.get upper_bounds U
                let LCM = lcm
                let constraints_on_bounds = Array.map2 (fun c t -> t <== (Int ((n-1)/(LCM/c)))) 
                let make_conjunct2 conjunct =
                    match conjunct with
                       | UpperBound (num, t) when num<>coefficient_U && t<>term_U
                        -> Some ( (t * (Int (LCM/num)) <== term_L * (Int (LCM/coefficient_L))) )
                       | LowerBound (num, t) when num<>coefficient_L && t<>term_L
                        -> Some ( (term_U * (Int (LCM/coefficient_U)) <== t * (Int (LCM/num))) )
                       | _ -> None
                let c1 = (l_coeffs, lower_bounds) ||> constraints_on_bounds 
                let c2 = (u_coeffs, upper_bounds) ||> constraints_on_bounds 
                let c3 = residual.conjuncts |> (Array.choose make_conjunct2)
                let c4 = [| Div ( term_L * (Int (LCM/coefficient_L)), LCM) <== Div ( term_L * (Int (LCM/coefficient_L)), LCM) |]
                [c1; c2; c3; c4 ] |> Array.concat |> Cube
               | cube -> Cube ([|if cube.apply_model M then True else False|])
        open_conjuncts + residual 
                           

//let LazyMbp (f: Expr) var (M: Map<Expr, Expr>) =
    
    

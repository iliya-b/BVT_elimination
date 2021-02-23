module BVTProver.Mbp
//open BVTProver
open System
open BVTProver.Bvt
open Formula
open Microsoft.Z3
open RewriteRules
     
let (|+) (|Pattern1|_|) (|Pattern2|_|) =
    let (|UnionPattern|_|) e =
        match e with
            | Pattern1 a | Pattern2 a -> Some(a)
            | _ -> None
    (|UnionPattern|_|)
    
let ctx = new Context()
let bvt = BVT(ctx, 8u, 8)

type RuleZ(Pattern1, SideCondition, rule_type) =
    let (|Pattern|_|) t = Pattern1 t

    member this.match_expr(e: Formula) =
        match e with
            | Pattern t when SideCondition (t, e) -> 0
            | _ -> 1
type LazyMbp () =

        
    member this.MbpZ (bounded_variable: string) (M: Map<string, int>)  (cube: Cube) =
        let x = Var bounded_variable
        let (|ThisVar|_|) (expr: Term) =
            match expr with
                | t when t=x -> Some()
                | _ -> None

        
        let (|ConstDivision|_|) (expr: Term) : (Term*int) option = 
                match expr with
                    | Div (t, d) when t.contains (Var bounded_variable) -> Some (t, d)
                    | _ -> None         
         
         
        let (|UpperBoundWithDivision|_|) (conjunct: Formula) =  // such that f(x) div b <= term
                match conjunct with
                    | Le(ConstDivision (f, b), d) when not (d.contains x) && M |= (d <== Div(Term.Max, b))
                     -> Some(f, b, d)
                    | _ -> None
        let (|LowerBoundWithDivision|_|) (conjunct: Formula) =  // such that f(x) div b > term
                match conjunct with                                        // todo: refactor side conditions
                    | Lt(d, ConstDivision (f, b)) when not (d.contains x) && M |= (d <! Div(Term.Max, b))
                     -> Some(f, b, d)
                    | _ -> None
        let (|AnyBoundWithDivision|_|) = (|UpperBoundWithDivision|_|) |+ (|LowerBoundWithDivision|_|)
            
        let (|TautologicalInequality|_|) (conjunct: Formula) =
                match conjunct with
                    | AsLe(AsMult(t1, ThisVar | ThisVar, t1), t2) -> Some(t1, t2)
                    | _ -> None
                           
        let (|Rule1|_|) (cube: Cube) =
            if cube.each_matches (|TautologicalInequality|_|) then
                Some(cube)
            else
                None

            
        let (|Rule3|_|) (cube: Cube) = cube.some_matches (|AnyBoundWithDivision|_|)
        let (|Rule2|_|) = (|Rule2|_|) M x 
                
        let (open_conjuncts, residual) = cube.split bounded_variable

        let residual: Cube =
            match residual with
              | Rule1 _ -> residual
              | Rule2 (lcm, bounds) ->
                let a, b = Array.partition BoundingInequality.is_upper bounds
                let u_coeffs, upper_bounds = a |> (Array.map BoundingInequality.tuplify) |> Array.unzip
                let l_coeffs, lower_bounds = b |> (Array.map BoundingInequality.tuplify) |> Array.unzip
                
                let (|Bounds|_|) = (|Bounds|_|) x
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
                       | Upper(num, t) when num<>coefficient_U && t<>term_U
                        -> Some ( (t * (Int (LCM/num)) <== term_L * (Int (LCM/coefficient_L))) )
                       | Lower (num, t) when num<>coefficient_L && t<>term_L
                        -> Some ( (term_U * (Int (LCM/coefficient_U)) <== t * (Int (LCM/num))) )
                       | _ -> None
                let c1 = (l_coeffs, lower_bounds) ||> constraints_on_bounds 
                let c2 = (u_coeffs, upper_bounds) ||> constraints_on_bounds 
                let c3 = residual.conjuncts |> (Array.choose (|Bounds|_|) ) |> (Array.choose make_conjunct2)
                let c4 = [| Div ( term_L * (Int (LCM/coefficient_L)), LCM) <== Div ( term_L * (Int (LCM/coefficient_L)), LCM) |]
                [c1; c2; c3; c4 ] |> Array.concat |> Cube
               | cube -> Cube ([|if cube.apply_model M then True else False|])
              | Rule3 T ->
                  let rew = match T with
                                | Le(ConstDivision (f, b), d) when not (d.contains x) && M |= (d <== Div(Term.Max, b))
                                                                     -> [| f <== (d+Term.One)*(Int b)-Term.One;
                                                                          d <== Div(Term.Max, b) |]
                                | LowerBoundWithDivision (f, y, g) -> [| (g+Term.One)*(Int y)-Term.One <! f
                                                                         g <== Div(Term.Max, y) |]
                                | _ -> failwith "unexpected"
                              
                  [ (Array.except [T] cube.conjuncts); rew ] |> Array.concat |> Cube |> (this.MbpZ bounded_variable M)
                  
        open_conjuncts + residual 
                           

//let LazyMbp (f: Expr) var (M: Map<Expr, Expr>) =
    
    

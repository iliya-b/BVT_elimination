module BVTProver.Mbp
//open BVTProver
open System
open BVTProver.Bvt
open Formula
open Microsoft.Z3
open RewriteRules.Rule1
open RewriteRules.Rule2
open RewriteRules.Rule3


let rec MbpZ (bounded_variable: string) (M: Map<string, int>) (cube: Cube) =
        let x = Var bounded_variable
        let (|Rule1|_|) = (|Rule1|_|) M x
        let (|Rule2|_|) = (|Rule2|_|) M x
        let (|Rule3|_|) = (|Rule3|_|) M x

        let (open_conjuncts, residual) = cube.split bounded_variable

        let residual: Cube =
            match residual with
            | Rule1 _ -> residual
            | Rule2 (lcm, bounds) ->
                let a, b =
                    Array.partition BoundingInequality.is_upper bounds

                let u_coeffs, upper_bounds =
                    a
                    |> (Array.map BoundingInequality.tuplify)
                    |> Array.unzip

                let l_coeffs, lower_bounds =
                    b
                    |> (Array.map BoundingInequality.tuplify)
                    |> Array.unzip

                let (|Bounds|_|) = (|Bounds|_|) x

                let exact_bound a b =
                    (a, b)
                    ||> Array.map2 (fun n (t: Term) -> (t.interpret M) * (lcm / n))
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

                let constraints_on_bounds =
                    Array.map2 (fun c t -> t <== (Int((n - 1) / (LCM / c))))

                let make_conjunct2 conjunct =
                    match conjunct with
                    | Upper (num, t) when num <> coefficient_U && t <> term_U ->
                        Some
                            ((t
                              * (Int(LCM / num))
                              <== term_L * (Int(LCM / coefficient_L))))
                    | Lower (num, t) when num <> coefficient_L && t <> term_L ->
                        Some
                            ((term_U
                              * (Int(LCM / coefficient_U))
                              <== t * (Int(LCM / num))))
                    | _ -> None

                let c1 =
                    (l_coeffs, lower_bounds) ||> constraints_on_bounds

                let c2 =
                    (u_coeffs, upper_bounds) ||> constraints_on_bounds

                let c3 =
                    residual.conjuncts
                    |> (Array.choose (|Bounds|_|))
                    |> (Array.choose make_conjunct2)

                let c4 =
                    [| Div(term_L * (Int(LCM / coefficient_L)), LCM)
                       <== Div(term_L * (Int(LCM / coefficient_L)), LCM) |]

                [ c1; c2; c3; c4 ] |> Array.concat |> Cube
            | cube -> Cube([| if cube.apply_model M then True else False |])
            | Rule3 (T, conjunct) ->
                let rew =
                    match T with
                    | Upper_ (f, b, d) ->
                        [| f <== (d + Term.One) * (Int b) - Term.One
                           d <== Div(Term.Max, b) |]
                    | Lower_ (f, y, g) ->
                        [| (g + Term.One) * (Int y) - Term.One <! f
                           g <== Div(Term.Max, y) |]

                [ (Array.except [ conjunct ] cube.conjuncts)
                  rew ]
                |> Array.concat
                |> Cube
                |> (MbpZ bounded_variable M)

        open_conjuncts + residual


//let LazyMbp (f: Expr) var (M: Map<Expr, Expr>) =

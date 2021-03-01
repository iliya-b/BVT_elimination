module BVTProver.MathHelpers

let rec gcd (a:int, b:int) =
    match b with
       | x when x = 0 -> a
       | _ -> gcd (b, a % b)

let rec lcm (a:int, b:int) =
    (a * b) / gcd (a,b)

let rec lcmlist (list: int list) =
    match list with
        | [] -> 1
        | [a] ->  a
        | [a;b] ->  lcm(a,b)
        | h::t  ->  lcm(h, lcmlist t)
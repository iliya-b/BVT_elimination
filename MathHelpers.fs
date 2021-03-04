module BVTProver.MathHelpers

let rec gcd (a:int, b:int) =
    if b=0 then
        a
    else
        gcd(b, a % b)

let lcm (a:int, b:int) = // todo handle overflow or  
    (a * b) / gcd (a, b)

let lcmlist (list: int list) = List.reduce (fun a b -> lcm(a, b)) list
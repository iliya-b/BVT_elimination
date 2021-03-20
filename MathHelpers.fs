module BVTProver.MathHelpers

let rec gcd (a, b) =
    if b=0u then
        a
    else
        gcd(b, a % b)

let lcm (a, b) = // todo handle overflow or  
    (a * b) / gcd (a, b)

let lcmlist list = List.reduce (fun a b -> lcm(a, b)) list
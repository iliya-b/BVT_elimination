module BVTProver.MathHelpers

let rec internal gcd (a, b) =
    if b=0u then
        a
    else
        gcd(b, a % b)

let internal lcm (a, b) = ( (uint64 a) * (uint64 b) |> uint32 ) / gcd (a, b)

let internal lcmlist list = List.reduce (fun a b -> lcm(a, b)) list


let internal pown_2 (power: uint32) = pown (uint64 2) (int32 power)
 
 
 
let internal (%%) a b = // python-like mod
    let c = a % b
    if c < 0u then
        b + c
    else
        c
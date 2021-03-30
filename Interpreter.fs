module BVTProver.Interpreter
open System.Collections.Generic
open BVTProver
open Helpers
open MathHelpers
open FormulaActions
open Continuations

type private InterpretedValue =
    | Bool of bool
    | Integer of uint32*uint32

let private int_func func x y =
            match x, y with
            | Integer (a, a_len), Integer (b, b_len) when a_len=b_len -> 
                let value = func (uint64 a) (uint64 b)
                let modulo = uint64 (pown_2 a_len)
                Integer (uint32 (value % modulo), a_len)
            | _ -> unexpected ()
            
let private bool_func func x y =
            match x, y with
            | Integer (a, a_len), Integer (b, b_len) when a_len=b_len -> 
                Bool (func a b)
            | _ -> unexpected ()
            
let private bool_op func x y =
            match x, y with
            | Bool a, Bool b -> Bool (func a b)
            | _ -> unexpected ()
        
let private extract x a b =
            match x with
            | Integer (d, _) ->
                let s = b - a + 1
                let n = ((1u <<< s) - 1u) &&& (d >>> (a-1))
                Integer (n, uint32 s)
            | _ -> unexpected ()
            
let private zero_extend t d =
             match t with
             | Integer(t, size) -> Integer(t, size+(uint32 d))
             | _ -> unexpected ()

let private expr_interpreter (model: IDictionary<string, uint32>) =
 
        formula_mapper
            (bool_func (=))
            (bool_func (<=))
            (bool_func (<))
            (bool_func (<=))
            (bool_func (<))
            (bool_op (&&))
            (bool_op (||))
            (bool_op (fun a b -> (not a) || b))
            (bool_op (=))
            (fun _ _ -> unexpected ()) // cannot interpret \exists
            (function Bool b -> Bool (not b) | _ -> unexpected ())
            (Bool true)
            (Bool false)
            (fun name s -> Integer (model.[name], s) )
            (int_func (*))
            (int_func (+))
            (int_func (&&&))
            (int_func (|||))
            (int_func (fun a b -> a>>>(int b))) // todo
            (int_func (fun a b -> a<<<(int b)))
            (fun bits size -> Integer (bits, size))
            zero_extend
            extract
            (fun _ _if _else -> unexpected ()) // todo
            (int_func (/))
            (function | Integer (a, s) ->
                          Integer ( (pown_2 s)  - a % (pown_2 s) , s)
                      | _ -> unexpected ())


let interpret_term model T =
    let res = fold (expr_interpreter model) (fun x -> x) (Term T)
    match res with
    | Integer (d, size) -> (d, size)
    | _ -> unexpected ()

let (|=) model F =
    let res = fold (expr_interpreter model) (fun x -> x) (Formula F)
    match res with
    | Bool b -> b
    | _ -> unexpected ()
                        
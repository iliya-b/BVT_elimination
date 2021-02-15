module Program
open System
open Microsoft.FSharp.Quotations

open System.Collections.Generic
open Microsoft.Z3
open Microsoft.Z3
open ZFormula
open Microsoft.Z3
exception ParseError of string
         
    
//    static member (+) (t1, t2) =
//        PLUS(t1, t2)
//    static member (*) (t1, t2) =
//        MULT(t1, t2)
//    static member (/) (t1, t2) =
//        DIVIDE(t1, t2)
//    static member (-) (t1, t2) =
//        MINUS(t1, t2)
//    static member (<<<) (t1, t2) =
//        BITSHIFT_LEFT(t1, t2)

let ctx = new Context()

let inline (~-) (t: BoolExpr) = ctx.MkNot(t)
let inline (-*) (t1: BitVecExpr) (t2: BitVecExpr) = ctx.MkBVSub(t1, t2)
let inline (+*) (t1: BitVecExpr) (t2: BitVecExpr) = ctx.MkBVAdd(t1, t2)
let inline (=*) (t1: BitVecExpr) (t2: BitVecExpr) = ctx.MkEq(t1, t2)
let inline (<=*) (t1: BitVecExpr) (t2: BitVecExpr) = ctx.MkBVULE(t1, t2)
let inline (>=*) (t1: BitVecExpr) (t2: BitVecExpr) = ctx.MkBVUGE(t1, t2)
let inline (>*) (t1: BitVecExpr) (t2: BitVecExpr) = ctx.MkBVUGT(t1, t2)
let inline (<*) (t1: BitVecExpr) (t2: BitVecExpr) = ctx.MkBVULT(t1, t2)

let n = 8u
let nn = 8
let _0 = ctx.MkBV(0, n)
let _1 = ctx.MkBV(1, n)

let rec contains (t: Expr) (var: BitVecExpr) =
    let var_name = var.FuncDecl.Name
    match t with
        | Var name -> var_name.ToString()=name
        | :? BitVecExpr as t -> Array.fold (fun acc t -> acc || contains t var) false t.Args
        | _ -> failwith "unexpected term" 


let getPremises conclusion (var: BitVecExpr) =
    let var_check t y z = contains t var && not (contains y var) && not (contains z var)
    let var_check2 t1 t2 y = contains t1 var && contains t2 var && not (contains y var)
    // t(x) - a terms containing x, y/z - x-free terms, a/b - any term
    match conclusion with
        | Le(Plus(t, y), z) when var_check t y z -> [
            [t <=* z-*y; y <=* z] // add1
            [t <=* z-*y; _0-*y <=* z] // add2 
            [_0-*y <=* t; y <=* z; -(y =* _0)] // add3
          ]
        | Ge(Plus(t, y), z) when var_check t y z -> [
            [t >=* z-*y; z <=* y-*_1]; // add4
            [t >=* z-*y; t <=* _0-*y-*_1; -(y =* _0)] // add5 
            [y =* _0; z <=* t] // add6
            [-(y =* _0); z <=* y-*_1; var <=* _0-*y-*_1] // add7
          ]
        | Le(Plus(t1, y), t2) when var_check2 t1 t2 y -> [
            [ y <=* t2 -* t1; t1 <=* t2; ]; // bothx1
            [ y <=* t2 -* t1; _0-*t1 <=* y; ];  // bothx2
            [ _0-*t1 <=* y; t1 <=* t2; -(t1 =* _0)] // bothx3
          ]
        | Equals(a, b) -> [ [a <=* b; b <=* a] ] // eq
        | Not(Equals(a, b)) -> [ [a <* b];  [a >* b]  ] // neq
        | Not(Le(a, b)) -> [ [b <=* a-*_1; _1 <=* a] ] // nule
        | Le(Minus(_0, t), y) when var_check2 t t y -> [ [_0-*y <=* t] ] // inv
        | Le(y, Minus(_0, t)) when var_check2 t t y -> [ [t <=* _0-*y] ] // inv
        | Le(Mult(Int k1, Var x), Mult(Int k2, Var _x)) when x=var.FuncDecl.Name.ToString() && _x=var.FuncDecl.Name.ToString()
         -> [ [var <=* ctx.MkBV( ((pown 2 nn) * k1 / k2), n) ] ] // bothx4
        | _ -> []
        

    
let is_this_variable term varname =
    match term with
        | Var v -> v.ToString().Equals(varname)
        | _ -> false



                                               
let term_to_str (term: Expr) =
    match term with
        | Var name -> name.ToString()
        | Int num -> num.ToString()
        | expr -> expr.ToString()
        
let rec formula_to_str (formula: Expr): string =
    match formula with
        | And (a, b) -> "And(" + formula_to_str(a)+", "+formula_to_str(b)+")" 
        | Or (a, b) -> "Or(" + formula_to_str(a)+", "+formula_to_str(b)+")"
        | True -> "True"
        | False -> "False"
        | Exists(name, F) -> "Exists(" + name.ToString() + ", " + (formula_to_str F) + ")"
        | Equals (t1, t2) ->  term_to_str(t1) + "==" + term_to_str(t2)

let rec DNF formula = // приводит бескванторную формулу в DNF
    match formula with
        | And (p1, p2) -> match DNF p1 with
                              | Or (a1, a2) -> DNF (ctx.MkOr( ctx.MkAnd(p2, a1), ctx.MkAnd(p2, a2) ))
                              | other -> match DNF p2 with
                                             | Or _ -> DNF (ctx.MkAnd(p2, other))
                                             | _ -> ctx.MkAnd (p1, p2)
        | Or (d1, d2) -> ctx.MkOr (DNF d1, DNF d2)                                     
        | (True | False | (Equals _)) as literal  -> literal
        | _ -> raise (ParseError "OR, AND, = are only available")
        
let simplify formula =
    match formula with
        | And(True, v1) -> v1
        | And(v1, True) -> v1
        | And(_, False) -> ctx.MkFalse()
        | And(False, _) -> ctx.MkFalse()
        | Or(True, _) -> ctx.MkTrue()
        | Or(_, True) -> ctx.MkTrue()
        | Or(v1, False) -> v1
        | Or(False, v1) -> v1
        | v -> v
        
let rec Eliminate formula (quantified_variable: string) : BoolExpr = // устраняет переменную из бескванторной формулы 

    let rec _Eliminate conjunctions = // устраняет переменную в каждой конъюкции

        let make_conjunction list =
           let rec loop list (acc: Option<Expr>) =
               match list with
               | (Equals(Var v1, (_ as v2))) :: tail when v1 = quantified_variable  -> if acc.IsSome then
                                                                                                    simplify (ctx.MkAnd(ctx.MkEq(acc.Value, v2), simplify (loop tail acc)))
                                                                                                  else
                                                                                                    simplify (loop tail (Some (v2 :> Expr)))
               | formula :: tail -> simplify (ctx.MkAnd( simplify(formula), simplify (loop tail acc)))
               | [] -> ctx.MkTrue()
           loop list None
        
        let rec make_disjunction conjunctions =
            match conjunctions with
                | head :: tail ->  simplify (ctx.MkOr(make_conjunction head, make_disjunction tail))
                | [] -> ctx.MkFalse()
                
        make_disjunction conjunctions
        
    let rec flat_conjunction f = // представляет конъюкцию массивом литералов
       match f with
            | And (_ as p1, (_ as p2)) -> (flat_conjunction p1) @ (flat_conjunction p2)
            | Equals(v2, Var v1) when v1 = quantified_variable -> [ctx.MkEq((ctx.MkBVConst(v1, n)), v2)] // fix order of terms 
            | (True | False | (Equals _)) as literal -> [literal] 
            | Or _ -> raise (ParseError "Not DNF")
            | _ -> raise (ParseError "OR, AND, = are only available")
                        
            
    let rec extract_conjunctions f = // представляет DNF формулу массивом конъюкций
        match f with
            | Or (Or _ as p1, (Or _ as p2)) -> (extract_conjunctions p1) @ (extract_conjunctions p2)
            | Or (_ as p1, (Or _ as p2)) -> (flat_conjunction p1) :: (extract_conjunctions p2)
            | Or (Or _ as p1, (_ as p2)) -> (flat_conjunction p2) :: (extract_conjunctions p1)
            | Or (_ as p1, (_ as p2)) -> [flat_conjunction p1] @ [flat_conjunction p2]
            | other -> [ flat_conjunction other ]
            | _ -> raise (ParseError "OR, AND, = are only available")
    
                
            
    formula |> DNF |> extract_conjunctions |> _Eliminate
   
let mutable total_quantifier = 2
let rec EliminateAllQuantifiers (formula: BoolExpr) = // устраняет все кванторы \exists из формулы 
    match formula with
        | Exists(name, F) -> total_quantifier <- total_quantifier-1
                             Eliminate (EliminateAllQuantifiers F) ("(:var " + (total_quantifier.ToString()) + ")")
        | (True | False | Equals _) as literal -> literal
        | And(p1, p2) -> ctx.MkAnd(EliminateAllQuantifiers p1, EliminateAllQuantifiers p2)
        | Or(p1, p2) -> ctx.MkOr(EliminateAllQuantifiers p1, EliminateAllQuantifiers p2)
        | v -> v
    
       

let rec Rewrite cube var model  =
    // todo: assert cube is cube
    // todo: assert model |= cube
    match cube with
        | Lt(term, Mult(Int _, Var x)) when x=var -> cube
        | Le(Mult(num, Var x), term)  when x=var -> cube // num is INT ?
        | cube -> let list = (getPremises cube (ctx.MkBVConst(var, n)))
                  if List.length list = 0 then
                      ctx.MkFalse()
                  else
                      let p = List.tryPick (fun _premises -> List.fold (fun result p ->
                                                                            let q = Rewrite p var model
                                                                            if result.IsSome (*&& model |= q*) then
                                                                                Some (ctx.MkAnd(result.Value, q))
                                                                            else
                                                                                None) (Some (ctx.MkTrue())) _premises) list
                      match p with
                            | Some x -> x
                            | None -> ctx.MkFalse()
                                  
                                  
                                  
                                       
                                    
                      
[<EntryPoint>]
let main argv =
    let x = ctx.MkBVConst("x", n)
    let y = ctx.MkBVConst("y", n)
    
    let a = ctx.MkBVConst("a", n)
    let b = ctx.MkBVConst("b", n)
    
                
        
    let n = uint32 8

    let f = ctx.MkBV(3, 9u)

    
    let formula = ctx.MkExists([|x|], ctx.MkAnd( ctx.MkExists([|y|], ctx.MkOr(ctx.MkEq(x, y), ctx.MkEq(x, a))), ctx.MkAnd(ctx.MkEq(x, a), ctx.MkEq(x, b) )))
    
    let eliminated_formula = EliminateAllQuantifiers formula
    
    let solver = ctx.MkSolver()
    solver.Add(ctx.MkIff(formula, eliminated_formula))
    if solver.Check() = Status.SATISFIABLE then
        printfn "OK"
    else 
        printfn "FAIL"

    printf "Your formula: %s\n" (formula_to_str formula)
    printf "\nFree formula: %s\n" (formula_to_str (eliminated_formula))
    (* Example:
        Your formula: Exists(x, And(Exists(y, Or(x==y, x==a)), And(x==a, x==b)))
        Free formula: a==b
    *)
        
    0
    



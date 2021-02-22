module BVTProver.BvtElimination
open BVTProver.Formula
open Microsoft.Z3
exception ParseError of string

let ctx = new Context()
let is_this_variable term varname =
    match term with
        | Var v -> v.ToString().Equals(varname)
        | _ -> false                                 
        
let rec DNF formula = // приводит бескванторную формулу в DNF
    match formula with
        | And args -> And (Array.map DNF args)  // todo
        | Or args -> Or (Array.map DNF args)                                     
        | (True | False | (Equals _)) as literal  -> literal
        | _ -> raise (ParseError "OR, AND, = are only available")      
let simplify formula =
    match formula with
        | And [|True; v1|]
        | And [|v1; True|] -> v1
        | And [| False; _ |] 
        | And [|  _; False |] -> False
        | Or [|True; _|] 
        | Or [| _; True|] -> True
        | Or [| v1; False|] 
        | Or [| False; v1 |] -> v1
        | v -> v      
let rec Eliminate formula (quantified_variable) : Formula = // устраняет переменную из бескванторной формулы 

    let rec _Eliminate conjunctions = // устраняет переменную в каждой конъюкции

        let make_conjunction list =
           let rec loop list (acc: Option<Term>) =
               match list with
               | (Equals((Var _) as v1, (_ as v2))) :: tail when v1 = quantified_variable  -> if acc.IsSome then
                                                                                                    simplify (And([| Equals(acc.Value, v2); simplify (loop tail acc) |]))
                                                                                              else
                                                                                                    simplify (loop tail (Some v2))
               | formula :: tail -> simplify (And( [| simplify(formula); simplify (loop tail acc) |] ))
               | [] -> True
           loop list None
        
        let rec make_disjunction conjunctions =
            match conjunctions with
               | head :: tail ->  simplify (Or([| make_conjunction head; make_disjunction tail |]))
               | [] -> False
                
        make_disjunction conjunctions
        
    let rec flat_conjunction f = // представляет конъюкцию массивом литералов
       match f with
            | And args -> Array.fold (fun acc e -> acc @ (flat_conjunction e)) [] args
            | Equals(v2, ((Var _) as v1)) when v1 = quantified_variable -> [Equals(v1, v2)] // fix order of terms 
            | (True | False | (Equals _)) as literal -> [literal] 
            | Or _ -> raise (ParseError "Not DNF")
            | _ -> raise (ParseError "OR, AND, = are only available")
                        
            
    let rec extract_conjunctions f = // представляет DNF формулу массивом конъюкций
        match f with
//            | Or (Or _ as p1, (Or _ as p2)) -> (extract_conjunctions p1) @ (extract_conjunctions p2)
//            | Or (_ as p1, (Or _ as p2)) -> (flat_conjunction p1) :: (extract_conjunctions p2)
//            | Or (Or _ as p1, (_ as p2)) -> (flat_conjunction p2) :: (extract_conjunctions p1)
//            | Or (_ as p1, (_ as p2)) -> [flat_conjunction p1] @ [flat_conjunction p2]
            | other -> [ flat_conjunction other ] // todo
            | _ -> raise (ParseError "OR, AND, = are only available")
    
                
            
    formula |> DNF |> extract_conjunctions |> _Eliminate
   
let rec EliminateAllQuantifiers (formula: Formula) = // устраняет все кванторы \exists из формулы 
    match formula with
        | Exists(name, F) -> let body = (EliminateAllQuantifiers F)
                             Eliminate body name
        | (True | False | Equals _) as literal -> literal
        | And args -> And( Array.map EliminateAllQuantifiers args )
        | Or args ->  Or( Array.map EliminateAllQuantifiers args )
        | v -> v
                                             
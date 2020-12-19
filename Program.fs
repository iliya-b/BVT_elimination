// Learn more about F# at http://fsharp.org

open System

open System.Collections.Generic
open Microsoft.Z3

exception ParseError of string

type Term =
    | EXP2 of Term
    | LOG2 of Term
    | PLUS of Term*Term
    | MINUS of Term*Term
    | INT of int
    | DIVIDE of Term*int
    | VAR of string
    
    | BITSHIFT_LEFT of Term*Term
    
type FORMULA =
    | LT of Term*Term
    | GT of Term*Term
    | EQUALS of Term*Term
    | TRUE
    | FALSE
    
    | AND of FORMULA * FORMULA
    | OR of FORMULA * FORMULA
    | NOT of FORMULA
    | IMPLIES of FORMULA * FORMULA
    | EXISTS of Term * FORMULA  // Term must be only VAR
    | ALL of Term * FORMULA


let a = AND(TRUE, FALSE)


let is_this_variable term varname =
    match term with
        | VAR v -> v.Equals(varname)
        | _ -> false



                                               
let term_to_str term =
    match term with
        | VAR name -> name
        | INT num -> num.ToString()
let rec formula_to_str formula =
    match formula with
        | AND (a, b) -> ("And(" + formula_to_str(a)+", "+formula_to_str(b)+")"); 
        | OR (a, b) -> ("Or(" + formula_to_str(a)+", "+formula_to_str(b)+")"); 
        | TRUE -> "True"
        | FALSE -> "False"
        | EXISTS(VAR name, F) -> "Exists(" + name + ", " + (formula_to_str F) + ")"
        | EQUALS (t1, t2) ->  term_to_str(t1) + "==" + term_to_str(t2)

let rec DNF formula = // приводит бескванторную формулу в DNF
    match formula with
        | AND (p1, p2) -> match DNF p1 with
                              | OR (a1, a2) -> DNF (OR( AND(p2, a1), AND(p2, a2) ))
                              | other -> match DNF p2 with
                                             | OR _ -> DNF (AND(p2, other))
                                             | _ -> AND (p1, p2)
        | OR (d1, d2) -> OR (DNF d1, DNF d2)                                     
        | (TRUE | FALSE | (EQUALS _)) as literal  -> literal
        | _ -> raise (ParseError "OR, AND, = are only available")
        
let simplify formula =
    match formula with
        | AND(TRUE, v1) -> v1
        | AND(v1, TRUE) -> v1
        | AND(_, FALSE) -> FALSE
        | AND(FALSE, _) -> FALSE
        | OR(TRUE, _) -> TRUE
        | OR(_, TRUE) -> TRUE
        | OR(v1, FALSE) -> v1
        | OR(FALSE, v1) -> v1
        | v -> v
        
let rec Eliminate formula (quantified_variable: string) = // устраняет переменную из бескванторной формулы 

    let rec _Eliminate conjunctions = // устраняет переменную в каждой конъюкции

        let make_conjunction list =
           let rec loop list (acc: Option<Term>) =
               match list with
               | (EQUALS(VAR v1, (_ as v2))) :: tail when v1 = quantified_variable  -> if acc.IsSome then
                                                                                        simplify (  AND(EQUALS(acc.Value, v2), simplify (loop tail acc)))
                                                                                       else
                                                                                        simplify (loop tail (Some v2))
               | formula :: tail -> simplify (AND( simplify(formula), simplify (loop tail acc)))
               | [] -> TRUE
           loop list None
        
        let rec make_disjunction conjunctions =
            match conjunctions with
                | head :: tail ->  simplify (OR(make_conjunction head, make_disjunction tail))
                | [] -> FALSE
                
        make_disjunction conjunctions
        
    let rec flat_conjunction f = // представляет конъюкцию массивом литералов
       match f with
            | AND (_ as p1, (_ as p2)) -> (flat_conjunction p1) @ (flat_conjunction p2)
            | EQUALS(v2, VAR v1) when v1 = quantified_variable -> [EQUALS((VAR v1), v2)] // fix order of terms 
            | (TRUE | FALSE | (EQUALS _)) as literal -> [literal] 
            | OR _ -> raise (ParseError "Not DNF")
            | _ -> raise (ParseError "OR, AND, = are only available")
                        
            
    let rec extract_conjunctions f = // представляет DNF формулу массивом конъюкций
        match f with
            | OR (OR _ as p1, (OR _ as p2)) -> (extract_conjunctions p1) @ (extract_conjunctions p2)
            | OR (_ as p1, (OR _ as p2)) -> (flat_conjunction p1) :: (extract_conjunctions p2)
            | OR (OR _ as p1, (_ as p2)) -> (flat_conjunction p2) :: (extract_conjunctions p1)
            | OR (_ as p1, (_ as p2)) -> [flat_conjunction p1] @ [flat_conjunction p2]
            | other -> [ flat_conjunction other ]
            | _ -> raise (ParseError "OR, AND, = are only available")
    
                
            
    formula |> DNF |> extract_conjunctions |> _Eliminate
   
let rec EliminateAllQuantifiers formula = // устраняет все кванторы \exists из формулы 
    match formula with
        | EXISTS(VAR name, F) -> Eliminate (EliminateAllQuantifiers F) name
        | (TRUE | FALSE | EQUALS _) as literal -> literal
        | AND(p1, p2) -> AND(EliminateAllQuantifiers p1, EliminateAllQuantifiers p2)
        | OR(p1, p2) -> OR(EliminateAllQuantifiers p1, EliminateAllQuantifiers p2)
        | v -> v


[<EntryPoint>]
let main argv =

    let x = VAR "x"
    let y = VAR "y"
    
    let a = VAR "a"
    let b = VAR "b"
   
    
    
    let formula = EXISTS(x, AND( EXISTS(y, OR(EQUALS(x, y), EQUALS(x, a))), AND(EQUALS(x, a), EQUALS(x, b) )))
    
    let printed_formula = formula_to_str formula
    let eliminated_formula = EliminateAllQuantifiers formula

    printf "Your formula: %s\n" printed_formula
    printf "\nFree formula: %s\n" (formula_to_str (eliminated_formula))
    (* Example:
        Your formula: Exists(x, And(Exists(y, Or(x==y, x==a)), And(x==a, x==b)))
        Free formula: a==b
    *)
    0
    

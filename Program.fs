// Learn more about F# at http://fsharp.org

open System

open Microsoft.Z3


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
    
//type DNF = 
let a = AND(TRUE, FALSE)


let is_this_variable term varname =
    match term with
        | VAR v -> v.Equals(varname)
        | _ -> false

let rec unpack conjunction (quantified_variable: string) =
    let rec find conjunction = 
        match conjunction with // looking for a literal containing quantified variable: x = 7, x = var2 
            | AND (_, ((EQUALS (VAR t1, (_ as term))) | (EQUALS ((_ as term), VAR t1)))  ) when t1.Equals(quantified_variable) && not (is_this_variable term quantified_variable)  -> Some term
            | AND (((EQUALS (VAR t1, (_ as term))) | (EQUALS ((_ as term), VAR t1))), _) when t1.Equals(quantified_variable)  && not (is_this_variable term quantified_variable) -> Some term
            | AND((AND _ as t1), _)  -> find t1
            | AND(_, (AND _ as t1))  -> find t1 // does it work как задумывалось?
    let term = find conjunction
    term // todo: replace x with this term
                                                    
let rec Eliminate formula =
    formula
    
    
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
        | EQUALS (t1, t2) -> "eq(" + term_to_str(t1) + ", " + term_to_str(t2)+ ")"

let rec DNF formula =
    match formula with
        | AND (p1, p2) -> match DNF p1 with
                              | OR (a1, a2) -> DNF (OR( AND(p2, a1), AND(p2, a2) ))
                              | other -> match DNF p2 with
                                             | OR _ -> DNF (AND(p2, other))
                                             | _ -> AND (p1, p2)
        | OR (d1, d2) -> OR (DNF d1, DNF d2)                                     
        | (TRUE | FALSE | (EQUALS _)) as literal  -> literal
        | (ALL _ | EXISTS _ | IMPLIES _ | NOT _ | LT _ | GT _) -> printf "OR, AND, = are only available"; TRUE
        



[<EntryPoint>]
let main argv =

    let x = VAR "x"
    let y = VAR "y"
    
    let a = VAR "a"
    let b = VAR "b"
    
    
    let formula = OR(AND(EQUALS(a, b), EQUALS(x, y)), OR(AND(OR(EQUALS(x, b), AND(EQUALS(y, a), EQUALS(x, y))), EQUALS(x, a)), AND(EQUALS(x, y), TRUE)))
    
    let printed_formula = formula_to_str formula
    let printed_dnf = formula_to_str (DNF formula)
    
    printf "%s" printed_formula
    printf "\n%s" printed_dnf
    0
    
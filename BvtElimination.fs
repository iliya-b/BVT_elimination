module BVTProver.BvtElimination
open BVTProver.BvtPatterns
open Microsoft.Z3
exception ParseError of string

let ctx = new Context()
let is_this_variable term varname =
    match term with
        | Var v -> v.ToString().Equals(varname)
        | _ -> false                                 
        
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
   
let rec EliminateAllQuantifiers (formula: BoolExpr) (total_quantifiers: int ) = // устраняет все кванторы \exists из формулы 
    match formula with
        | Exists(name, F) -> let body = (EliminateAllQuantifiers F (total_quantifiers+1))
                             Eliminate body ("(:var " + ( (total_quantifiers+1).ToString() ) + ")")
        | (True | False | Equals _) as literal -> literal
        | And(p1, p2) -> ctx.MkAnd(EliminateAllQuantifiers p1 total_quantifiers, EliminateAllQuantifiers p2 total_quantifiers)
        | Or(p1, p2) -> ctx.MkOr(EliminateAllQuantifiers p1 total_quantifiers, EliminateAllQuantifiers p2 total_quantifiers)
        | v -> v
                                             
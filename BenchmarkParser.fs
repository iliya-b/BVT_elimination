module BVTProver.BenchmarkParser


open System
open System.Collections.Generic
open System.Diagnostics
open System.IO
open BVTProver
open BVTProver.RewriteRules
open Helpers
open Formula
open FormulaActions
open Interpreter
open Bvt
open Mbp
open Microsoft.Z3
open Z3Patterns
open Microsoft.Z3
open Mbp
open Rule3

open System
open System.IO
let private extract_num  (e: KeyValuePair<FuncDecl, Expr>) =
    match e.Value with
    | :? BitVecNum as e -> Some e
    | _ -> None
    
    
// good: /Volumes/MyPassport/bvt/QF_BV/2018-Goel-hwbench/QF_BV_bv_bv_eq_sdp_v5_cc_ref_max.smt2
let private is_some_lia_conjuncts i path =
    async {
        if path="/Volumes/MyPassport/bvt/QF_BV/2019-Mann/ridecore-qf_bv-bug.smt2" then
            return (path, 0)
        else 
            let ctx = new Context()
            let j = i
           
           
            let benchmark_formulae = ctx.ParseSMTLIB2File(path)
            
            let arithmetic_part = benchmark_formulae |> Array.filter is_LIA_z3
            let depth = Array.map (z3_depth_formula 0) arithmetic_part
            if Array.length depth = 0 then
                return (path, 0)
            else
                return (path, Array.max depth)
    }



     
let private is_bv_model (model: Model) =
    Seq.forall (fun (e: KeyValuePair<FuncDecl, Expr>) -> e.Value.IsBV) model.Consts      
            
let private get_bv_model (ctx: Context) expressions =
    let model =
        expressions
        |> ctx.MkAnd
        |> get_model_z3 ctx
    match model with
    | Some model when is_bv_model model -> Some (convert_model model)
    | _ -> None

let private rewritable_linear_count (ctx: Context) expressions =
    let model = get_bv_model ctx expressions
    match model with
    | Some model ->
        expressions
        |> Seq.filter is_LIA_z3
        |> Seq.map (convert_z3 >> as_formula)
        |> Seq.filter (fun f -> Seq.exists (fun x -> (Rewrite x model f) |> Option.isSome) model.Keys)
        |> Seq.length
    | _ -> 0
        

let rule3_is_applicable model x conjunct =
    let norm = Rewrite x model conjunct
    match norm with
    | Some (Rule3 model x _) ->
        let i = 0
        true
    | _ -> false

let  get_model_z3_many (ctx: Context) (expr: BoolExpr[]) =    
    let solver = ctx.MkSolver()

    solver.Add (expr)
    if solver.Check()=Status.SATISFIABLE then
        Some solver.Model
    else
        None    
let get_serialized_model file =
    eprintfn "%s" file
    let ctx = new Context()
    let expressions = ctx.ParseSMTLIB2File file
    
    let model =
        expressions
        |> get_model_z3_many ctx
        
    match model with
    | Some model when is_bv_model model ->
        Some (file, model.ToString())
    | _ -> None
let find_matching_conjuncts file =
    let ctx = new Context()
    let expressions = ctx.ParseSMTLIB2File file
    match get_bv_model ctx expressions with
    | Some model ->
        let res =
            Seq.filter is_LIA_z3 expressions
            |> Seq.map (convert_z3>>as_formula)
            |> Seq.allPairs model.Keys
            |> Seq.exists (fun (x, e) -> rule3_is_applicable model x e)
        res
    | None -> false
    
let total_rewritable files =
        let ctx = new Context()
        files
        |> Seq.map (ctx.ParseSMTLIB2File)
        |> Seq.map (rewritable_linear_count ctx)
        |> Seq.take 15
        |> Seq.sum
let doLazyMbp (ctx: Context) (model: Model) benchmark_formulae =
        
    let is_tautology_z3 = is_tautology_z3 ctx
        
    
    if Seq.exists (extract_num>>Option.isNone) model.Consts then
                        false // if some variable is not in BVT (e.g. a propositional var)
    else
                        
                        let inline And (fs: BoolExpr list) = fs |>  List.map (function | :? BoolExpr as e -> e | _ -> unexpected ()) |> Array.ofList |> ctx.MkAnd 
                        let inline exists x f = ctx.MkExists([| x |], f)
                        let inline (=>.) f1 f2 = ctx.MkImplies(f1, f2)
                        let inline (<=>.) f1 f2 = ctx.MkIff(f1, f2)
                        
                        let x = model.ConstDecls.[0]
                        let benchmark_formulae = List.ofArray benchmark_formulae
                        let res = Z3_LazyMbp ctx model x benchmark_formulae
                        let var_value =
                            (model.Consts
                            |> Seq.find (fun (e: KeyValuePair<FuncDecl, Expr>) -> e.Key=x)).Value :?> BitVecNum
                        
                        let x = (x.Name.ToString (), var_value.SortSize) |> ctx.MkBVConst
                        let naive_mbp = List.map (fun (e: BoolExpr) -> e.Substitute ( x , var_value) :?> BoolExpr) benchmark_formulae
                        let in_formula = And benchmark_formulae
                        let ss = List.map (fun x -> x.ToString()) res
                        let ss2 = List.map (fun x -> x.ToString()) benchmark_formulae
                        let is_approximation = is_tautology_z3 (And res =>. exists x in_formula)
                        let is_equiv = is_tautology_z3 (And res <=>. exists  x in_formula)
                        let naive_mbp_is_correct = is_tautology_z3 (And naive_mbp =>. exists x in_formula)
                        let naive_mbp_is_equiv = is_tautology_z3 (And naive_mbp <=>. exists x in_formula)
                        let is_naive = is_tautology_z3 (And res <=>. And naive_mbp)
                        if not is_naive && List.length res > 0 then
                            let k = 1
                            true
                        else
                            false
let findDeepLinearBenchmarks =     
    let files = File.ReadAllLines("/Volumes/MyPassport/bvt/sat_list2.txt")
    let data =
        files
        |> Seq.mapi is_some_lia_conjuncts
        |> Seq.take 1000
        |> Async.Parallel
        |> Async.RunSynchronously
        |> Seq.filter (snd>>((>=) 4))
        |> Seq.map fst
        |> List.ofSeq
    let s = String.Join(",", List.map (fun x -> x.ToString()) data)
    s
//    let ctx = new Context()
//   // 1.9G exclude: /Volumes/MyPassport/bvt/QF_BV/2019-Mann/ridecore-qf_bv-bug.smt2
//    // 1M: /Volumes/MyPassport/bvt/QF_BV/Sage2/bench_10590.smt2
//    let mutable found = []
//
//    for file in files do
//        let file = (file.Split ":").[0]
//        let file = "/Volumes/MyPassport/bvt/QF_BV/" + file
//
//        let benchmark_formulae = ctx.ParseSMTLIB2File(file)
//        
//        let arithmetic_part = benchmark_formulae |> Array.filter is_LIA_z3
//        let depth = Array.map (z3_depth_formula 0) arithmetic_part
//        if Array.length depth > 0 then
//            let max_depth = Array.max depth
//            printfn "%d" max_depth
//            ignore max_depth
//        else
//            ignore 0

//        solver.Add benchmark_formulae 
//        let s = solver.Check ()
        
//        File.WriteAllText ("/tmp/z3_model.smt.txt", solver.Model.ToString())
//        let cube = List.ofArray <| Array.map (convert_z3>>as_formula) arithmetic_part

               
//        let i = 0
//        
//        let raw_model = solver.Model.Consts |> List.ofSeq
//        
//        let vars = raw_model |> List.map (fun x -> x.Key.Name.ToString(), (x.Value :?> BitVecNum).UInt)
//        let model = vars |> dict
//        let x = (raw_model.[i].Key.Name.ToString(), (raw_model.[i].Value :?> BitVecNum).SortSize)
//        let res = LazyMbp model x cube
        
//        ignore res
    
        
//        let opt =
//            try
//                let vars = raw_model |> List.map (fun x -> x.Key.Name.ToString(), (x.Value :?> BitVecNum).UInt)
//                let model = vars |> dict
//                (List.ofArray <| Array.map (convert_z3>>as_formula) benchmark_formulae, model)
//                |> Some
//            with
//            | :? System.Exception as e -> None
//        
//        match opt with
//        | None -> ignore 0
//        | Some (cube, model) ->
//            let our_formula = z3fy_expression ctx (cube |> And |> Formula) :?> BoolExpr
//            let their_formula = ctx.MkAnd benchmark_formulae
//            let z3_check = ctx.MkIff (our_formula, their_formula)
//            solver.Reset ()
//            solver.Add (ctx.MkNot z3_check)
//            let status = solver.Check ()
//                
//            if status=Status.SATISFIABLE then
//                let s1 = our_formula.ToString()
//                let s2 = their_formula.ToString()
//                printfn "%s" file
//            else
//                let x = (raw_model.[i].Key.Name.ToString(), (raw_model.[i].Value :?> BitVecNum).SortSize)
//                if 1u=snd x then
//                    ignore 0
//                else
//                    let res = LazyMbp model x cube
//                    if res=[] then
//                        ignore 0
//                    else
//                        let naive_mbp = List.map (x --> model) cube
//                        
//                        let ss = List.map (fun x -> x.ToString()) res
//                        let ss2 = List.map (fun x -> x.ToString()) cube
//                        let is_approximation = is_tautology (And res => Exists (Var x, And cube))
//                        let is_equiv = is_tautology (And res <=> Exists (Var x, And cube))
//                        let naive_mbp_is_correct = is_tautology (And naive_mbp => Exists (Var x, And cube))
//                        let naive_mbp_is_equiv = is_tautology (And naive_mbp <=> Exists (Var x, And cube))
//                        let is_naive = is_tautology (And res <=> And naive_mbp)
//                        ignore ss
//            // exception: bit vector length must be >0  
        
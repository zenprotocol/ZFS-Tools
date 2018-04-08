module Hints

open FStar.Util
open FSharpx.Functional.Prelude
//module FSXL = FSharpx.Collections.List
module FSXM = FSharpx.Collections.Map

type Hint = hint
type Hints = hints
type HintsDB = hints_db

let hint_name  (hint:Hint) : string = hint.hint_name
let hint_fuel  (hint:Hint) : int    = hint.fuel
let hint_ifuel (hint:Hint) : int    = hint.ifuel

// Should use FSXL.catOptions, but https://github.com/fsprojects/FSharpx.Collections/issues/89
let inline catOptions (xs:Option<'a> list) = List.choose id xs

(* A map from names of terms to a list of it's hints *)
type HintsMap = Map< string, list<Hint> >

let hints_to_hintsMap : Hints -> HintsMap =
    catOptions
    >> List.groupBy hint_name
    >> Map.ofList

let read_hints: string -> option<HintsMap> = 
    read_hints
    >> Option.map (fun {hints=hints} -> hints_to_hintsMap hints)

let sumBy (f: Hint -> int) : HintsMap -> int =
    Map.fold (fun count _ hints -> count + List.sumBy f hints) 0
    
(* The number of queries in a single hint *)
let num_queries : Hint -> int = function
    | {unsat_core = None} -> 0
    | {unsat_core = Some unsatcores} -> List.length unsatcores

(* The number of queries used by a single identifier *)
let num_queries_ident (ident:string) : HintsMap -> option<int> =
    Map.tryFind ident 
    >> Option.map (List.sumBy num_queries)

(* The total number of queries used by all hints *)
let total_num_queries : HintsMap -> int =
    sumBy num_queries

(* Gets the fuel used by a single identifier *)
let query_fuel (ident : string) : HintsMap -> option<int> =
    Map.tryFind ident
    >> Option.map (List.sumBy hint_fuel)

(* The total fuel used by all hints *)
let total_fuel : HintsMap -> int =
    sumBy hint_fuel

(* Gets the ifuel used by a single identifier *)
let query_ifuel (ident : string) : HintsMap -> option<int> =
    Map.tryFind ident
    >> Option.map (List.sumBy hint_ifuel)

(* The total ifuel used by all hints *)
let total_ifuel : HintsMap -> int =
    sumBy hint_ifuel
    
    
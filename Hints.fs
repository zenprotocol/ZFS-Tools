module Hints

open FStar.Util
module M = FSharpx.Collections.Map


type Hint = hint
type Hints = hints
type HintsDB = hints_db

let read_hints: string -> option<HintsDB> = read_hints

(* A map from names of terms to a list of it's hints *)
type hintsMap = Map< string, list<Hint> >

let hints_to_hintsMap : Hints -> hintsMap =
    let rec aux (hintsMap : hintsMap) : Hints -> hintsMap = function
        | [] -> hintsMap
        | None::hs -> aux hintsMap hs
        | Some ({hint_name = hint_name} as h) :: hs -> 
            let hintsMap' = hintsMap |> M.insertWith List.append hint_name [h]
            aux hintsMap' hs
    
    aux Map.empty

(* Gets the fuel used by a given identifier *)
let fuel_used (hintsMap : hintsMap) (ident : string) : int =
    match Map.tryFind ident hintsMap with
    | None -> 0
    | Some hs -> hs |> List.sumBy (fun h -> h.fuel)

(* Gets the ifuel used by a given identifier *)
let ifuel_used (hintsMap : hintsMap) (ident : string) : int =
    match Map.tryFind ident hintsMap with
    | None -> 0
    | Some hs -> hs |> List.sumBy (fun h -> h.fuel)
    
let z3_queries_used (hintsMap : hintsMap) (function_name : string) : int =
    let num_queries : Hint -> int = function 
        | {unsat_core = None} -> 0
        | {unsat_core = Some uc} -> List.length uc 
    
    match Map.tryFind function_name hintsMap with
    | None -> 0
    | Some hs -> hs |> List.sumBy num_queries


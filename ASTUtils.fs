module ASTUtils

open FSharpx
open System
open FStar.Parser.AST
open FStar.Ident
open FStar.Const
open FSharpx.Collections.List
open FSharpx.Functional.Prelude
open FStar.Range

module BU = FStar.Util
module PI = FStar.Parser.ParseIt
module PD = FStar.Parser.Dep
module String = FSharpx.String
module PP = FStar.Pprint
module TD = FStar.Parser.ToDocument


type Comment = string * FStar.Range.range
type Fragment = list<decl> * list<Comment>
type AST = modul * list<Comment>

let mapFst (f: 'a -> 'c) (fst: 'a, snd: 'b) : 'c * 'b = 
    f fst, snd
let mapSnd (f: 'b -> 'c) (fst: 'a, snd: 'b) : 'a * 'c =
    fst, f snd 

let lid_of_string: string -> lid =
    lid_of_str
let string_of_path: path -> string =
    String.concat "."
let string_of_lid: lid -> string =
    path_of_lid >> string_of_path
let module_name_of_file: string -> string =
    PD.module_name_of_file
let module_lid_of_file: string -> lid =
    module_name_of_file >> lid_of_string

let lid_of_module: modul -> lid = function
    | Module (lid, _)
    | Interface(lid, _, _) -> lid

let decls_of_modul: modul -> list<decl> = function
    | Module(_, decls)
    | Interface(_, decls, _) -> decls

let decls_to_modul: lid -> list<decl> -> modul =
    curry Module

let decls_to_interface: lid -> bool -> list<decl> -> modul =
    curry3 Interface >> flip

let frag_to_ast: lid -> Fragment -> AST =
    mapFst << decls_to_modul

(* Gets the module name of an AST as a string *)
let get_module_lid : AST -> lid = lid_of_module << fst

let get_module_name: AST -> string = get_module_lid >> string_of_lid

(* parenthesises a term *)
let paren tm = mk_term (Paren tm) tm.range tm.level

(* constructs a term at the range and level of the first argument. 
   eg. mk_term_at Paren (tm1:term) tm1 => (tm1) *)
let mk_term_at ({range=range; level=level}: term) (term':term') : term =
    mk_term term' range level

(* converts an integer n to an unsigned integer literal at the level of the second argument. *)
let mk_int_at (term:term) (n:int) : term = 
    Const_int(string n, None)
    |> Const
    |> mk_term_at term
    
(*  qualifies ident with nsstr as a namespace. 
    nsstr is of the form "Ab.Bc.Cd.De..." where each namespace identifier must begin with an uppercase.
    eg. add_ns_ident "Foo.Bar" baz => Foo.Bar.baz *)
let qual_ns_ident (nsstr:string) (ident:ident) : lid = 
    let firstCharIsUpper : string -> bool = Seq.head >> Char.IsUpper
    
    let ns_ids = nsstr |> String.splitChar [|'.'|]
    let ns:list<ident> = ns_ids |> Array.map (fun (s:string) -> {idText=s; idRange=ident.idRange})
                                |> Array.toList
    if not (ns_ids |> Array.forall firstCharIsUpper)
        then invalidArg nsstr "Invalid namespace identifier format";
    
    {ns=ns; ident=ident; nsstr=nsstr; str=String.concat "." [nsstr; ident.idText]}

(* equivalent to add_ns_ident, where the second argument is a string. *)
let qual_ns_str (nsstr:string): string -> lid = id_of_text >> qual_ns_ident nsstr

(* Increments a term by n. eg x => (inc n (x)) *)
let mk_inc (term:term, n:int) : term =
    if n < 0
        then failwith "Negative increments should be impossible"
    elif n = 0
        then term
    else
        let n = n |> mk_int_at term
        let inc = qual_ns_str "Zen.Cost" "inc"
                  |> Var
                  |> mk_term_at term
        mkExplicitApp inc [n; paren term] term.range
        |> paren

(* similar of FStar.Parser.ToDocument.unparen, since the .fsi does not expose it *)
let rec unparen: term -> term = function
  | {tm=Paren t} -> unparen t
  | t -> t

(******************************************************************************)
(* Checking Idents                                                            *)
(******************************************************************************)

let fsharpkeywords : Set<string> = 
    Set.ofList FStar.Extraction.ML.Syntax.fsharpkeywords

let is_reserved_name (name: string) : bool =
    fsharpkeywords
    |> Set.contains name

let is_potential_cli_conflict s =
       String.startsWith "get_" s
    || String.startsWith "set_" s

let reserved_module_names = ["FStar"; "Prims"; "Zen"; "ZFStar"]

let is_reserved_module_abbrev (abbrev: string) : bool =
    reserved_module_names
    |> List.contains abbrev

let check_name (s: string) : unit =
    if is_reserved_name s
        then failwithf "\"%s\" is not permitted as an identifier" s
    elif is_potential_cli_conflict s
        then failwith "Identifiers may not start with \"get_\" or \"set_\""
    else ()

let check_ident : ident -> unit =
    check_name << text_of_id

let check_const: sconst -> unit = function
    | Const_effect -> failwith "unexpected Const_effect in pattern"
    | Const_reify -> failwith "unexpected reify in pattern"
    | Const_reflect _ -> failwith "unexpected reflect in pattern"
    | _ -> ()

let rec check_pattern ({pat=pat}: pattern) : unit = 
    match pat with
    | PatWild -> ()
    | PatConst c -> check_const c
    | PatApp (p, ps) ->
        check_pattern p;
        ps |> List.iter check_pattern
    | PatVar(ident, _)
    | PatTvar(ident, _) -> check_ident ident
    | PatName _ -> ()
    | PatList pats
    | PatTuple(pats, _)
    | PatVector pats
    | PatOr pats ->
        pats |> List.iter check_pattern
    | PatRecord pats ->
        pats |> List.iter (check_pattern << snd)
    | PatAscribed (p,_) -> check_pattern p
    | PatOp ident ->
        check_ident ident

let check_binder ({b=binder}: binder) = 
    match binder with
    | Variable ident
    | TVariable ident
    | Annotated(ident, _)
    | TAnnotated(ident, _) -> check_ident ident
    | NoName _ -> ()

let check_tycon tycon =
    match tycon with
    | TyconAbstract(ident, binders, _)
    | TyconAbbrev(ident, binders, _, _) ->
        check_ident ident;
        binders |> List.iter check_binder
    | TyconRecord   (ident, binders, _, fields) ->
        check_ident ident;
        binders |> List.iter check_binder;
        fields  |> List.iter(fun (ident, _, _) -> check_ident ident)
    | TyconVariant  (ident, binders, _, fields) ->
        check_ident ident;
        binders |> List.iter check_binder;
        fields  |> List.iter(fun (ident, _, _, _) -> check_ident ident)

let rec check_term ({tm=term}: term) : unit =
    match term with
    | Wild -> ()
    | Const c -> check_const c
    | Op(_, terms) -> terms |> List.iter check_term
    | Tvar _
    | Uvar _
    | Var _
    | Name _
    | Projector _ -> ()
    | Construct(_, terms) -> terms |> List.iter (check_term << fst) 
    | Abs(pats, term) -> pats |> List.iter check_pattern;
                         check_term term
    | App(term1, term2, _) -> check_term term1; check_term term2
    | Let(Mutable, _, _) -> failwith "Mutation is not permitted."
    | Let(_, letbindings, term) ->
        letbindings 
        |> List.iter begin function 
                     | (Some _, _) -> failwith "Attributes are not permitted."
                     | (None, (pattern, term)) -> check_pattern pattern;
                                                  check_term term 
                     end
        check_term term
    | LetOpen(_, term) -> check_term term
    | Seq(term1, term2) -> check_term term1; check_term term2
    | Bind(pat, term1, term2) -> check_pattern pat; 
                                 check_term term1; 
                                 check_term term2
    | If(term1, term2, term3)
    | IfBind(term1, term2, term3) -> check_term term1;
                                     check_term term2;
                                     check_term term3 
    | Match(term, branches) -> check_term term; 
                               branches |> List.iter check_branch
    | TryWith _ -> failwith "Try ... with ... is not currently implemented."
    | Ascribed(term1, term2, term3) -> check_term term1;
                                       check_term term2;
                                       term3 |> Option.iter check_term 
    | Record(term, fields) -> term |> Option.iter check_term;
                              fields |> List.iter (check_term << snd)
    | Project(term, _) -> check_term term
    | Product(binders, term)
    | Sum(binders, term) -> binders |> List.iter check_binder;
                                check_term term
    | QForall(binders, terms, term)
    | QExists(binders, terms, term) -> 
        binders |> List.iter check_binder;
        terms |> (List.iter check_term << List.concat);
        check_term term
    | Refine(binder, term) -> check_binder binder; check_term term
    | NamedTyp(ident, term) -> check_ident ident; check_term term
    | Paren term -> check_term term
    | Requires(term, _)
    | Ensures(term,_ ) -> check_term term
    | Labeled(term, _, _) -> check_term term
    | Discrim _ -> ()
    | Attributes _ -> failwith "Attributes are not permitted."
    | Antiquote _
    | Quote _
    | VQuote _ -> failwith "Quotations are not currently permitted" 
    
and check_branch: branch -> unit = function
    | (_, Some _, _) -> failwith "When clauses are not currently implemented." 
    | (pattern, None, term) -> check_pattern pattern; check_term term

let check_module_abbrev ({idText=abbrev}: ident) : unit =
    if not ^ is_reserved_module_abbrev abbrev then () 
    else failwithf "\"%s\" is not permitted as a module abbreviation." abbrev

let module_name_ok: list<string> -> bool =
    not << List.exists (flip List.contains reserved_module_names)
    
let check_module_lid (lid:lid): unit =
    if module_name_ok ^ path_of_lid lid then ()
    else failwith "`%s` is not permitted as a module name." ^ string_of_lid lid

let check_decl ({d=decl}: decl) =
    match decl with
    | TopLevelModule lid -> check_module_lid lid
    | Open _ -> ()
    | Include _ -> failwith "Includes are not permitted."
    | ModuleAbbrev(abbrev, _) -> check_module_abbrev abbrev
    | TopLevelLet(Mutable, _) -> failwith "Mutation is not permitted."
    | TopLevelLet(_, letBindings) ->
        letBindings |>! List.iter (check_pattern << fst)
                    |>  List.iter (check_term << snd)  
    | Main _ -> failwith "Unexpected: Main decl"
    | Tycon(true, _) -> failwith "User-defined effects are not permitted."
    | Tycon(false, tycons) -> tycons |> List.iter (check_tycon << fst) 
    | Val(_, v) -> check_term v
    | Exception _ -> failwith "User-defined exceptions are not permitted."
    | NewEffect _
    | SubEffect _ -> failwith "User-defined effects are not permitted."
    | Pragma _ -> failwith "Pragmas are not permitted."
    | Fsdoc _ -> ()
    | Assume _ -> failwith "Assumes are not permitted."
    | Splice _ -> failwith "Splices are not permitted."

let check_module (modul: modul): unit =
    modul
    |>! (check_module_lid << lid_of_module)
    |>  (List.iter check_decl << decls_of_modul)

let check_ast: AST -> unit = check_module << fst

(******************************************************************************)
(* Cost Elaboration                                                           *)
(******************************************************************************)

let rec pat_cost {pat=pat} = 
    match pat with
    | PatWild
    | PatConst _
    | PatVar _
    | PatName _
    | PatTvar _
    | PatOp _ -> 1
    | PatAscribed (pat, _) -> 
        pat_cost pat
    
    | PatList pats
    | PatVector pats
    | PatTuple (pats, _)
    | PatOr pats ->
        pats |> List.map pat_cost
             |> List.sum
    
    | PatRecord fields ->
        let _, field_pats = List.unzip fields
        field_pats |> List.map pat_cost
                   |> List.sum
    
    | PatApp (patn, arg_pats) ->
        let patn_cost = pat_cost patn
        let arg_pats_costs = List.map pat_cost arg_pats
        let sum_arg_pats_costs = List.sum arg_pats_costs
        patn_cost + sum_arg_pats_costs

(* returns a tuple of the elaborated branch, and the cost of the branch *)
let rec elab_term
    ({tm=tm; range=range; level=level} as branch)
    : term * int = 
    
    let mk_term_here (tm':term') : term = 
        mk_term tm' range level
    
    match tm with
    | Wild (* The hole, [_] *)
    | Const _ (* Effect constants,
                 The unit constant [()],
                 Boolean constants [true, false],
                 Integer constants [7, 0x6F, 13UL],
                 Character constants ['c'],
                 Float constants [1.23],
                 ByteArray constants ["c"B, "q"B, "?"B]
                    Note that the bytes are in reversed order.
                    eg. 'c' = 0x0063, but the bytearray is [|0x63uy; 0x00uy|].
                 String constants ["this is a string constant"]
                 Range constants (not denotable in source code)
                 Reification constants [reify]
                 Reflection constants [lident1?.reflect, lident2?.reflect] *)
    | Tvar _ (* Type variable names [ident1, ident2] *)
    | Uvar _ (* Universe variable. Should not be elaborated. *)
    | Var _  (* Variable names [lident1, lident2, Foo.Bar.baz] *)
    | Name _ (* Non-variable names; begin with uppercase. [Lident1, Foo.Bar.Baz] *)
        -> (branch, 0)
    | Projector (_, _) -> // terms like Cons?.hd, NOT THE SAME AS "Project"
        (branch, 1) 
    | Project (tm,lid) -> // terms like tm.lid
        let tm_elabed, tm_cost = elab_term tm
        let project = Project (tm_elabed, lid) |> mk_term_here
        (project, 1 + tm_cost)
            
    | Abs (patterns, expr) ->
        (* lambdas, eg. `fun [patterns] -> expr` *)
        let expr_elaborated = elab_term expr |> mk_inc
        let lambda_elaborated = Abs (patterns, expr_elaborated) |> mk_term_here
        (lambda_elaborated, 0)
    
    | Ascribed (expr1, expr2, None) -> (* [expr1 <: expr2] *)
        let expr1_elaborated, expr1_cost = elab_term expr1
        let ascribed_elaborated = Ascribed (expr1_elaborated, expr2, None) 
                                  |> mk_term_here
        (ascribed_elaborated, expr1_cost)
        
    | Op (op_name, args:list<term>) ->
        (* Operators. 
           [ Op ( "+", [x;y] ) ] 
           = [x + y] *)
        let args_elaborated, args_costs = 
            args |> List.map elab_term
                 |> List.unzip
        let op_term = Op (op_name, args_elaborated) |> mk_term_here
        let sum_args_cost = List.sum args_costs
        let num_args = List.length args
        let op_term_cost = num_args + sum_args_cost
        (op_term, op_term_cost)
    
    | App (expr1, expr2, imp) -> (* Application, eg. [expr1 (expr2)] *)
        let expr1_elaborated, expr1_cost = elab_term expr1
        let expr2_elaborated, expr2_cost = elab_term expr2
        let app_term = App (expr1_elaborated, expr2_elaborated, imp)
                       |> mk_term_here
        let app_term_cost = 1 + expr1_cost + expr2_cost
        (app_term, app_term_cost)
    
    | Construct (ctor_name : lid, ctor_args:list< term * imp >) ->
        (* Constructors. 
           [ Construct ( "Some", [x, Nothing] ) ] 
           = [Some x] *)
        let (ctor_args_terms, ctor_args_imps) : (list<term> * list<imp>) =
            List.unzip ctor_args
        let ctor_args_terms_elaborated, ctor_args_costs = 
            ctor_args_terms |> List.map elab_term
                            |> List.unzip
        let ctor_args_elaborated : list< term * imp > = 
            List.zip ctor_args_terms_elaborated 
                     ctor_args_imps 
        let construct_term = Construct (ctor_name, ctor_args_elaborated)
                             |> mk_term_here
        let sum_ctor_args_cost = List.sum ctor_args_costs
        let num_ctor_args = List.length ctor_args
        let construct_term_cost =
            sum_ctor_args_cost + num_ctor_args
        (construct_term, construct_term_cost)
    
    | Seq (expr1, expr2) -> (* Sequenced expression, eg. [expr1; expr2] *)
        let expr1_elaborated, expr1_cost = elab_term expr1
        let expr2_elaborated, expr2_cost = elab_term expr2
        let seq_tm = Seq (expr1_elaborated, expr2_elaborated) |> mk_term_here
        let seq_tm_cost = expr1_cost + expr2_cost
        (seq_tm, seq_tm_cost)
    
    | Bind (patn, expr1, expr2) -> 
        (* Bind patterns, eg. `let! patn = expr1 in expr2`
           desugared as `Zen.Cost.letBang expr1 (fun patn -> expr2)` *)
        let expr1_elaborated, expr1_cost = elab_term expr1
        let expr2_elaborated, expr2_cost = elab_term expr2
        let bind_term = Bind (patn, expr1_elaborated, expr2_elaborated)
                        |> mk_term_here
        let bind_term_cost = expr1_cost + expr2_cost + 2
        (bind_term, bind_term_cost)
    
    | IfBind (i, t , e) -> 
        (* `If! i then t else e`, 
           desugared as `Zen.Cost.ifBang i (fun i' -> if i' then t else e)` *)
        let i_elaborated, i_cost = elab_term i
        let t_elaborated, t_cost = elab_term t
        let e_elaborated, e_cost = elab_term e
        let if_bind = IfBind(i_elaborated, t_elaborated, e_elaborated)
                      |> mk_term_here
        let max_branch_cost = max t_cost e_cost
        let if_bind_cost = i_cost + max_branch_cost + 3
        (if_bind, if_bind_cost)
        
    
    | Paren expr -> (* Parenthesized expression, ie. [(expr)] *)
        let expr_elaborated, expr_cost = elab_term expr
        let paren_term = Paren expr_elaborated |> mk_term_here
        (paren_term, expr_cost)

    | Match (e1, branches) -> (* match e1 with | branches [0] | branches [1] ... | branches [last] *)
        let e1_elaborated, e1_cost = elab_term e1
        let (branches_patterns : list<pattern>), // the match cases
            (branches_when : list<( option<term> )>), // optional when clause, currently not enabled
            (branches_terms : list<term>) = // the term in each branch
                List.unzip3 branches
        
        let branches_patterns_costs = branches_patterns |> List.map pat_cost
        let sum_branches_patterns_costs = List.sum branches_patterns_costs
        let (branches_terms_elaborated : list<term>),
            (branches_terms_costs : list<int>) = 
                 branches_terms |> List.map elab_term
                                |> List.unzip  
        let max_branch_cost = List.max branches_terms_costs
        let match_cost = e1_cost + sum_branches_patterns_costs + max_branch_cost
        let branches_elaborated : list<branch> = 
            List.zip3 branches_patterns 
                      branches_when 
                      branches_terms_elaborated
        let match_term = Match (e1_elaborated, branches_elaborated) 
                         |> mk_term_here
        (match_term, match_cost)

    | Let (qualifier, pattern_term_pairs, expr1) -> (* let [patterns] = [terms] in expr1 *)
        let rec elab_pat_term_pair (attr, (pat, term)) =
            let term_elaborated, term_cost = elab_term term
            match pat with
            | { pat=PatApp _ } -> // functions must have annotated cost
                let inc_term_elaborated = mk_inc (term_elaborated, term_cost)
                ((attr, (pat, inc_term_elaborated)), 0)
            | { pat=PatAscribed (pat', _) } -> 
                //if the pattern has an ascription, retry with the ascribed pattern
                elab_pat_term_pair (attr, (pat', term))
                |> fun ((attr, (_, term)),cost) -> (attr, (pat, term)), cost
            | _ -> (attr, (pat, term_elaborated)), term_cost
        
        let pattern_term_pairs_elaborated, term_costs = 
            pattern_term_pairs |> List.map elab_pat_term_pair
                               |> List.unzip
        let sum_term_costs = List.sum term_costs
        let expr1_elaborated, expr1_cost = elab_term expr1
        let let_term = mk_term_here ^ Let ( qualifier,
                                            pattern_term_pairs_elaborated,
                                            expr1_elaborated )
        let let_cost = sum_term_costs + expr1_cost
        (let_term, let_cost)
            
    | Record (e1 : option<term>, fields: list<lid * term>) ->
        (* [ Record ( Some e1, [(lid2,e2); (lid3,e3); ...; (lidn,en)] ) ]
            = [ { e1 with lid2=e2; lid3=e3; ...; lidn=en } ],
           [ Record ( None, [(lid2,e2); (lid3,e3); ...; (lidn,en)] ) ]
            = [ { lid2=e2; lid3=e3; ...; lidn=en } ] *)
        
        let num_fields = List.length fields
        let (field_names, field_terms) : (list<lid> * list<term>) = 
            List.unzip fields      
        let (fields_elaborated, fields_costs) : (list<term> * list<int>) = 
            List.map elab_term field_terms 
            |> List.unzip           
        let fields_cost = List.sum fields_costs
        let fields_elaborated = (field_names, fields_elaborated) ||> List.zip
        let (e1_elaborated, e1_cost) : (option<term> * option<int>) = 
            match Option.map elab_term e1 with
            | Some (e1_cost, e1_elaborated) -> (Some e1_cost, Some e1_elaborated)
            | None -> (None, None)
        let record_cost =
            match e1_cost with
            | None -> num_fields + fields_cost
            | Some e1_cost -> num_fields + e1_cost + fields_cost
        let record_term = Record (e1_elaborated, fields_elaborated)
                          |> mk_term_here
        (record_term, record_cost)
        
    | If (cond_branch, then_branch, else_branch) ->
        let cond_branch_elabd, cond_branch_cost = elab_term cond_branch
        let then_branch_elabd, then_branch_cost = elab_term then_branch
        let else_branch_elabd, else_branch_cost = elab_term else_branch
        
        let if_term =
            If (cond_branch_elabd, then_branch_elabd, else_branch_elabd)
            |> mk_term_here
        let max_branch_cost = max then_branch_cost 
                                  else_branch_cost
        let if_term_cost = 3 + cond_branch_cost + max_branch_cost
        (if_term, if_term_cost)
        
    | LetOpen (module_name, expr) -> (* [let open module_name in expr] *)
        let expr_elaborated, expr_cost = elab_term expr
        let letopen_tm = LetOpen (module_name, expr_elaborated)
                         |> mk_term_here
        (letopen_tm, expr_cost)
    
    // try..with block; not currently permitted
    | TryWith _ -> failwith "try..with blocks are not currently implemented."
    | _ -> failwith ("unrecognised term" + branch.ToString() + ": please file a bug report")

(* Attaches an increment to tm. tm => inc tm n *)
let elab_term_node node =
    elab_term node |> mk_inc

let is_lemma_lid : lid -> bool = function
    | { ns=[]; ident={idText="Lemma"}; nsstr=""; str="Lemma" } -> true
    | _ -> false

let rec is_lemma_type : term' -> bool = function
    | Construct(lid, _) -> is_lemma_lid lid
    | Product(_, tm) -> is_lemma_type tm.tm
    | _ -> false

let is_lemma_val : decl -> bool = function
    | { d=Val(_, {tm=signature_tm}) } -> is_lemma_type signature_tm
    | _ -> false 

let is_lemma_pat : pattern' -> bool = function
    | PatAscribed(_, ({tm=ascription_type},_)) -> is_lemma_type ascription_type
    | _ -> false
    
let is_lemma_tll : decl -> bool = function
    | { d=TopLevelLet(_, [{pat=tll_patn}, _]) } -> // TODO: Should we allow recursion-recursion here?
            is_lemma_pat tll_patn
    | _ -> false

//elaborates a decl
let elab_decl ({d=d} as decl) =
    let d_elaborated = 
        match d with
        | Main tm -> Main (elab_term_node tm)
        | TopLevelLet (q,p) -> 
            if is_lemma_tll decl then d 
            else // Do not elaborate lemmas
                p |> List.map (mapSnd elab_term_node)
                  |> tuple2 q
                  |> TopLevelLet
        | Tycon (false, _) -> d
        | Tycon (true, _) -> failwith "effect declarations are not currently permitted"
        | Exception _ -> failwith "exceptions are not currently permitted"
        | NewEffect _ -> failwith "effect declarations are not currently permitted"
        | SubEffect _ -> failwith "effect declarations are not currently permitted"
        | Assume _ -> failwith "assumes are not currently permitted"
        | Pragma _ -> failwith "pragmas are not currently permitted"
        | Splice _ -> failwith "splices are currently permitted"
        | TopLevelModule _ | Open _ | Include _ | ModuleAbbrev _ | Val _ | Fsdoc _ -> d
    
    { decl with d = d_elaborated }

let name_of_decl : decl -> string = function
    | { d=Val(i, _) } -> i.idText
    | { d=TopLevelLet(_, pat_tm_pairs) } ->
        lids_of_let pat_tm_pairs 
        |> List.map (fun l -> l.str) 
        |> String.concat ", "
    | _ -> failwith "Please file a bug report: name_of_decl failed."

let rec elab_decls : list<decl> -> list<decl> = function
    | [] -> []
    | [d] -> [elab_decl d]
    | fst::snd::tl ->
        match snd.d with
        | TopLevelLet _ ->
            (* If we have a val and a top-level-let with the same name, 
               and the val is a lemma, do not elaborate the top-level-let. *)
            if is_lemma_val fst &&
               name_of_decl fst = name_of_decl snd
            then fst::snd::elab_decls tl
            else elab_decl fst :: elab_decls (snd::tl)
        | _ -> elab_decl fst :: elab_decls (snd::tl)
     
                        
let main_decl_val range = (* [val mainFunction : Zen.Types.mainFunction] *)
    let main_ident = id_of_text "mainFunction"
    let main_decl_val_term' = Var ^ qual_ns_str "Zen.Types" "mainFunction"
    let main_decl_val_term = mk_term main_decl_val_term' range Type_level
    let main_decl'_val = Val (main_ident, main_decl_val_term)
    { d=main_decl'_val; drange=range; doc=None; quals=[]; attrs=[] }

let main_decl_let range = (* [let mainFunction = MainFunc (CostFunc cf) main] *)     
    let main_ident = id_of_text "main"
    let main_term' = Var ^ lid_of_ns_and_id [] main_ident
    let main_term = mk_term main_term' range Expr
    
    let cf_ident = id_of_text "cf"
    let cf_term' = Var ^ lid_of_ns_and_id [] cf_ident
    let cf_term = mk_term cf_term' range Expr
    
    let costFunc_term' = Construct (qual_ns_str "Zen.Types" "CostFunc", [cf_term, Nothing])
    let costFunc_term = mk_term costFunc_term' range Expr
    
    let mainFunc_term' = 
        Construct ( qual_ns_str "Zen.Types" "MainFunc",
                    [ (paren costFunc_term, Nothing); (main_term, Nothing) ] )
    let mainFunc_term = mk_term mainFunc_term' range Expr
    
    let main_decl'_let = TopLevelLet ( NoLetQualifier, 
                                       [ { pat=PatVar (id_of_text "mainFunction", None);
                                           prange=range }, 
                                           mainFunc_term ] )
      
    { d=main_decl'_let; drange=range; doc=None; quals=[]; attrs=[] }

let main_decl' range = [ main_decl_val range; main_decl_let range ]
let main_decls = main_decl' FStar.Range.dummyRange

let map_decls (f: list<decl> -> list<decl>): modul -> modul = function
    | Module (lid, decls) -> Module (lid, f decls)
    | Interface (lid, decls, bool) -> Interface (lid, f decls, bool)

let cons_decls: list<decl> -> modul -> modul =
    map_decls << List.append

let cons_decl: decl -> modul -> modul =
    map_decls << cons 

let append_decls (decls: list<decl>): modul -> modul =
    map_decls (fun ds -> ds @ decls) 

let append_decl (decl: decl): modul -> modul =
    append_decls [decl]

let add_main_decl: modul -> modul =
    append_decls main_decls
     
let elab_module: modul -> modul =
    map_decls elab_decls

let elab_ast : AST -> AST =
    mapFst elab_module

let add_main_to_ast : AST -> AST =
    mapFst add_main_decl

let remove_module_name_decl: modul -> modul =
    let remove: list<decl> -> list<decl> = function
        | {d=TopLevelModule _}::decls
        | {d=Fsdoc _}::{d=TopLevelModule _}::decls
        | decls -> decls
    map_decls remove

let add_module_name_decl (m:modul): modul =
    m |> cons_decl { d=TopLevelModule (lid_of_module m)
                     drange=FStar.Range.dummyRange
                     doc=None
                     quals=[]
                     attrs=[] }

let remove_module_name: AST -> AST =
    mapFst remove_module_name_decl

let add_module_name: AST -> AST =
    mapFst add_module_name_decl


(******************************************************************************)
(* Printing                                                                   *)
(******************************************************************************)

let string_of_doc: PP.document -> string =
    PP.pretty_string 1.0 100

let parse_frag (fn: string): Fragment =
    match PI.parse (PI.Filename fn) with
    | PI.ASTFragment (BU.Inl modul, comments) ->
        decls_of_modul modul, comments
    | PI.ASTFragment (BU.Inr decls, comments) ->
        decls, comments
    | PI.Term _ -> 
        failwith "expected an AST fragment"
    | PI.ParseError (error, msg, r) -> 
        FStar.Errors.raise_error (error, msg) r

let parse_file (filename: string) : AST =
    FStar.Parser.Driver.parse_file filename

let modul_to_string: modul -> string =
    TD.modul_to_document >> string_of_doc

let ast_to_doc : AST -> PP.document =
    uncurry TD.modul_with_comments_to_document
    >> fst

let ast_to_string: AST -> string =
    ast_to_doc >> string_of_doc

// prints a module to a specified output channel
let print_modul' : modul -> FStar.Util.out_channel -> unit = 
    TD.modul_to_document >> PP.pretty_out_channel 1.0 100

// prints a module to stdout
let print_modul (m:modul) : unit =
    print_modul' m stdout

// prints an AST to a specified output channel
let print_ast' : AST -> FStar.Util.out_channel -> unit =
    ast_to_doc
    >> PP.pretty_out_channel 1.0 100

// prints an AST to stdout
let print_ast : AST -> unit =
    flip print_ast' stdout

let write_ast_to_file (filename:string): AST -> unit =
    ast_to_string 
    >> curry IO.File.WriteAllText filename
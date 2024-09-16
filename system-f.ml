
open List

let flatmap (f : 'a -> 'b list) (list : 'a list) : 'b list = flatten (map f list)

(******************************************************************************)
(* Important types *)

type cname = CN of string
type tname = TN of string option * int
type t =
  | TUnit
  | TInt
  | TBool
  | TVariable  of tvar  ref      (*     'x : (previously-)unknown type *)
  | TConstant  of tname          (*      x : known type, different from all other constants *)
  | TParam     of tname          (*     ?X : parameter to a universal type *)
  | TArrow     of t list * t     (* t -> t : function's type *)
  | TApplied   of cname * t list (*    t c : generic structure type *)
  | TUniversal of tname list * t (*   ∀X.t : polymorphic type -> term function *)
and tvar =
  | Linked  of tname * t         (* this variable has already been unified against *)
  | Unknown of tname             (* this variable is totally unknown *)

type 'v binding =
  | Term of 'v * t                     (* x:t : x has type t *)
  | Decl of tname                      (*   X : X is a generic type *)
type 'v tctx = TCtx of 'v binding list (*   Γ : contains a list of all types bound
                                        *       by a parent, and a mapping from
                                        *       vars -> their type
                                        *)

module TNameSet = Set.Make(
  struct
    type t = tname
    let compare (TN (_, id1)) (TN (_, id2)) = id2 - id1
  end
)

(******************************************************************************)
(* Logging, formatting, and debug *)

let latin = ["a";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n";"o";"p";"q";"r";"s";"t";"u";"v";"w";"x";"y";"z"]
let greek = ["α";"ꞵ";"γ";"δ";"ε";"ζ";"η";"θ";"κ";"μ";"ξ";"π";"σ";"τ";"χ";"ψ"] (* ambiguous ones removed *)

type namectx = NCtx of ((int * string) list * int) ref
let namectx_create () = NCtx (ref ([], 0))
let ctx_of (opt : namectx option) = Option.value opt ~default:(namectx_create ())
let fmt_tname ?nctx ?(is_generic = false) (TN (name_opt, id)) : string =
  if Option.is_none nctx then
    let id = string_of_int id in
    match name_opt with
    | Some name -> name ^ "_" ^ id
    | None      ->        "_" ^ id
  else
    let NCtx ctx = Option.get nctx in
    let table, alloc = !ctx in
    match assoc_opt id table with
    | Some already_formatted -> already_formatted
    | None ->
        match name_opt with
        | Some name ->
            let formatted = name ^ "_" ^ string_of_int id in
            ctx := (id, formatted)::table, alloc;
            formatted
        | None ->
            let alphabet  = if is_generic then greek else latin in
            let length    = length alphabet in
            let letteridx = alloc mod length in
            let suffixidx = alloc / length in
            let suffix    = if suffixidx = 0 then "" else string_of_int suffixidx in
            let formatted = nth alphabet letteridx ^ suffix in
            ctx := (id, formatted)::table, alloc + 1;
            formatted
let fmt_cname (CN name) = name

let print_derefs = true
let rec fmt_t ?nctx (t : t) : string =
  let nctx = ctx_of nctx in
  let fmt_t = fmt_t ~nctx in
  let fmt_constant = fmt_tname ?nctx:None ~is_generic:false in
  let fmt_generic = fmt_tname ~nctx ~is_generic:true in
  let fmt_tname = fmt_tname ~nctx ~is_generic:false in
  let rec simple_t (t : t) : bool =
    match t with
    | TUnit       -> true
    | TInt        -> true
    | TBool       -> true
    | TConstant _ -> true
    | TParam _    -> true
    | TVariable { contents = Unknown _     } -> true
    | TVariable { contents = Linked (_, t) } -> print_derefs || simple_t t
    | _ -> false
  in
  let open String in
  match t with
  | TUnit -> "unit"
  | TInt  -> "int"
  | TBool -> "bool"
  | TVariable { contents = Unknown name  } -> "'" ^ fmt_tname name
  | TVariable { contents = Linked (_, t) } ->
      if print_derefs
      then "[" ^ fmt_t t ^ "]"
      else       fmt_t t
  | TConstant name -> fmt_constant name
  | TParam name -> "?" ^ uppercase_ascii (fmt_generic name)
  | TArrow ([dom], cod) when simple_t dom -> fmt_t dom ^ " -> " ^ fmt_t cod
  | TArrow (doms, cod) ->
      let doms = concat ", " (List.map fmt_t doms) in
      "(" ^ doms ^ ") -> " ^ fmt_t cod
  | TApplied (c, [x]) when simple_t x -> fmt_t x ^ " " ^ fmt_cname c
  | TApplied (x, xs) ->
      let args = concat ", " (List.map fmt_t xs) in
      "(" ^ args ^ ") " ^ fmt_cname x
  | TUniversal (qs, inner) ->
      let quantified = concat " " (List.map fmt_generic qs) in
      "∀" ^ uppercase_ascii quantified ^ ". " ^ fmt_t inner

(******************************************************************************)
(* Accessors / Setters / Updaters / Predicates / Important utils *)

let tvar (tname : tname) : t = TVariable (ref (Unknown tname))

let id_count = ref (-1) (* pre-incremented *)
let genid () : int = incr id_count; !id_count
let genid _ : int = genid ()
let gentname _ : tname = TN (None, genid ())
let gentvar _ : t = tvar (gentname ())
let gentparam _ : t = TParam (gentname ())

let tname_id (TN (_, id)) = id
let map_tname_id (f : int -> int) (TN (name, id)) = TN (name, f id)

let is_linked (tvar : tvar) : bool =
  match tvar with
  | Linked _ -> true
  | Unknown _ -> false
let link (tvar : tvar ref) (linkto : t) =
  match !tvar with
  | Linked (name, t) -> failwith (fmt_tname name ^ "is already linked")
  | Unknown name -> tvar := Linked (name, linkto)
let of_tvar (tvar : tvar) : t =
  match tvar with
  | Linked (_, t) -> t
  | Unknown name -> failwith (fmt_tname name ^ " is not linked")

let tctx_get_opt (key : 'v) (TCtx tctx : 'v tctx) : t option =
  find_map (fun binding ->
    match binding with
    | Term (k, t) when k = key -> Some t
    | _ -> None
  ) tctx
let tctx_mem (key : 'v) (tctx : 'v tctx) : bool =
  Option.is_some (tctx_get_opt key tctx)
let tctx_get ?default (key : 'v) (tctx : 'v tctx) : t =
  let opt = tctx_get_opt key tctx in
  if Option.is_some default
  then Option.value opt ~default:(Option.get default)
  else Option.get opt
let tctx_cons (binding : 'v binding) (TCtx tctx : 'v tctx) : 'v tctx =
  TCtx (binding :: tctx)
let tctx_append (TCtx ctx0 : 'v tctx) (TCtx ctx1 : 'v tctx) : 'v tctx =
  TCtx (ctx0 @ ctx1)
let tctx_add_all (bindings : 'v binding list) (TCtx ctx : 'v tctx) : 'v tctx =
  TCtx (bindings @ ctx)

let concat_tname_sets (sets : TNameSet.t list) : TNameSet.t =
  fold_left TNameSet.union TNameSet.empty sets

(******************************************************************************)
(* Type system *)

let rec freevars_of_type (t : t) : TNameSet.t =
  let module Set = TNameSet in
  match t with
  | TConstant name -> Set.singleton name
  | TVariable { contents = Unknown name } -> Set.singleton name
  | TVariable ref -> freevars_of_type (of_tvar !ref)
  | TArrow (doms, cod) ->
      let fvdoms = concat_tname_sets (map freevars_of_type doms) in
      Set.union fvdoms (freevars_of_type cod)
  | TApplied (_, args) -> concat_tname_sets (map freevars_of_type args)
  | TUniversal (qs, inner) ->
      let fvinner = freevars_of_type inner in
      let bounds = Set.of_list qs in
      Set.diff fvinner bounds
  | _ -> Set.empty

let freevars_of_binding (binding : 'v binding) : TNameSet.t =
  match binding with
  | Decl name -> TNameSet.singleton name
  | Term (_, t) -> freevars_of_type t

let freevars_of_tctx (TCtx bindings) : TNameSet.t =
  concat_tname_sets (map freevars_of_binding bindings)

let rec occurs (tname : tname) (t : t) : bool =
  let occurs_lst = fold_left (fun a t -> a || occurs tname t) false in
  match t with
  | TVariable { contents = Unknown name } -> tname = name
  | TVariable { contents = Linked (name, t) } -> tname = name || occurs tname t
  | TConstant name -> tname == name
  | TParam name -> tname == name
  | TArrow (doms, cod) -> occurs_lst doms || occurs tname cod
  | TApplied (_, args) -> occurs_lst args
  | TUniversal (_, t) -> occurs tname t
  | _ -> false

let rec unify ?nctx (t1 : t) (t2 : t) =
  let unify t1 t2 =
    (* print_endline ("unifying " ^ fmt_t ?nctx t1 ^ " and " ^ fmt_t ?nctx t2); *)
    let result = unify ?nctx t1 t2 in
    (* print_endline ("done with " ^ fmt_t ?nctx t1 ^ " ~ " ^ fmt_t ?nctx t2); *)
    result
  in
  match t1, t2 with
  | TUnit, TUnit -> ()
  | TInt,  TInt  -> ()
  | TBool, TBool -> ()
  | TVariable v1, TVariable v2 when v1 == v2 -> ()
  | TVariable v1, TVariable v2 when is_linked !v2 && not (is_linked !v1) -> unify (of_tvar !v2) t1
  | TVariable ref, _ when not (is_linked !ref) ->
      let[@warning "-8"] Unknown name = !ref in
      if occurs name t2 then
        failwith (
          "failed occurs check: " ^ fmt_tname ?nctx name
          ^ " occurs in " ^ fmt_t ?nctx t2
        )
      else link ref t2
  | TVariable ref, _ when is_linked !ref -> unify t2 (of_tvar !ref)
  | _, TVariable _ -> unify t2 t1
  | TConstant name1, TConstant name2 when name1 = name2 -> ()
  | TArrow (doms1, cod1), TArrow (doms2, cod2) ->
      iter2 unify doms1 doms2;
      unify cod1 cod2
  | TApplied (x, xs), TApplied (y, ys) when x = y -> iter2 unify xs ys
  | _ ->
      let nctx = ctx_of nctx in
      failwith (
        "disallowed unification "
        ^ fmt_t ~nctx t1
        ^ " ~ "
        ^ fmt_t ~nctx t2
      )

let rec subst ?nctx (alist : (tname * t) list) (t : t) : t =
  (* print_endline ("(" ^ fmt_t ?nctx t ^ ")[");
  iter (fun (name, t) ->
    print_endline ("  " ^ fmt_tname ?nctx name ^ " := " ^ fmt_t ?nctx t )
  ) alist;
  print_endline "]"; *)
  let subst = subst ?nctx in
  let module Set = TNameSet in
  match t with
  | TVariable { contents = Unknown name } when mem_assoc name alist ->
      assoc name alist
  | TVariable ref when is_linked !ref -> subst alist (of_tvar !ref)
  | TParam name when mem_assoc name alist -> assoc name alist
  | TConstant name when mem_assoc name alist -> assoc name alist
  | TArrow (doms, cod) -> TArrow (map (subst alist) doms, subst alist cod)
  | TApplied (x, xs) -> TApplied (x, map (subst alist) xs)
  | TUniversal (qs, inner) ->
      let keys  = Set.of_list (map fst alist) in
      let setqs = Set.of_list qs in
      let errors = Set.inter keys setqs in
      if Set.cardinal errors != 0 then
        let nctx = ctx_of nctx in
        failwith (
          "scope error, cannot subst {"
          ^  String.concat ", " (map (fmt_tname ~nctx) (Set.to_list errors))
          ^ "} into "
          ^ fmt_t ~nctx t
        )
      else TUniversal (qs, subst alist inner)
  | _ -> t

let apply ?nctx (universal : t) (args : t list) =
  match universal with
  | TUniversal (qs, inner) -> subst ?nctx (combine qs args) inner
  | _ ->
      failwith (
        "tried to apply a non-universal type " ^ fmt_t ?nctx universal
      )

let instantiate ?nctx (t : t) =
  (* print_endline ("instantiating " ^ fmt_t ?nctx t); *)
  match t with
  | TUniversal (qs, inner) ->
      let alist = map (fun q -> q, gentvar ()) qs in
      subst ?nctx alist inner
  | _ -> t

let abstract ?nctx (t : t) (ctx : 'v tctx) : t =
  (* print_endline ("abstracting " ^ fmt_t ?nctx t); *)
  let fv_t   = freevars_of_type t in
  let fv_ctx = freevars_of_tctx ctx in
  let frees  = TNameSet.(diff fv_t fv_ctx |> to_list) in
  let newnames = map gentname frees in
  let generics = map2 (fun fv name -> (fv, TParam name)) frees newnames in
  TUniversal (newnames, subst ?nctx generics t)

;;
print_endline "Test type formatting:";

TUniversal ([TN (None, 0); (TN (None, 1))],
  TArrow(
    [TArrow ([TParam (TN (None, 0))], TParam (TN (None, 1)));
     TApplied (CN "list", [TParam (TN (None, 0))])],
    TApplied (CN "list", [TParam (TN (None, 1))])))

|> fmt_t
|> print_endline

;;

(******************************************************************************)
(* Type Checker and Inferencer
 * ---------------------------
 * This actually still uses HM type reconstruction, but the user can
 * express more complicated types via annotations
 *)

type vname = VN of string * int
type exp0 =
  | Unit0
  | Int0    of int
  | Var0    of vname
  | Call0   of exp0 * exp0 list
  | If0     of exp0 * exp0 * exp0
  | LetRec0 of vname * exp0 * exp0
  | Lambda0 of vname list * exp0
  | Annot0  of exp0 * t

type exp1 =
  | Unit1
  | Int1    of int
  | Var1    of t * vname
  | Call1   of t * exp1 * exp1 list
  | If1     of t * exp1 * exp1 * exp1
  | LetRec1 of t * vname * exp1 * exp1
  | Lambda1 of t * vname list * exp1

let fmt_vname (VN (name, id)) = name ^ "_" ^ string_of_int id
let fmt_exp0 ?nctx (exp : exp0) : string =
  let fmt_simple exp =
    match exp with
    | Unit0 -> "()"
    | Int0 i -> string_of_int i
    | Var0 name -> fmt_vname name
    | Lambda0 _ -> "λ..."
    | _ -> "..."
  in
  match exp with
  | Unit0     -> "()"
  | Int0 i    -> string_of_int i
  | Var0 name -> fmt_vname name
  | Call0 (f, args) ->
      fmt_simple f ^ " " ^ String.concat " " (map fmt_simple args)
  | If0 (c, y, n) ->
      "if " ^ fmt_simple c
      ^ " then " ^ fmt_simple y
      ^ " else " ^ fmt_simple n
  | LetRec0 (name, value, body) ->
      "let rec " ^ fmt_vname name ^ " = " ^ fmt_simple value
      ^ " in " ^ fmt_simple body
  | Lambda0 (ps, body) ->
      "λ" ^ String.concat " " (map fmt_vname ps) ^ " -> " ^ fmt_simple body
  | Annot0 (exp, t) -> "( " ^ fmt_simple exp ^ " :: " ^ fmt_t ?nctx t ^ " )"

let typeof (exp : exp1) : t =
  match exp with
  | Unit1 -> TUnit
  | Int1 _ -> TInt
  | Var1 (t, _) -> t
  | Call1 (t, _, _) -> t
  | If1 (t, _, _, _) -> t
  | LetRec1 (t, _, _, _) -> t
  | Lambda1 (t, _, _) -> t

let map_exp_t (f : t -> t) (exp : exp1) : exp1 =
  match exp with
  | Unit1 -> Unit1
  | Int1 i -> Int1 i
  | Var1 (t, name) -> Var1 (f t, name)
  | Call1 (t, func, args) -> Call1 (f t, func, args)
  | If1 (t, c, y, n) -> If1 (f t, c, y, n)
  | LetRec1 (t, name, value, body) -> LetRec1 (f t, name, value, body)
  | Lambda1 (t, ps, body) -> Lambda1 (f t, ps, body)

let fmt_exp1 ?nctx (exp : exp1) : string =
  let nctx = ctx_of nctx in
  let fmt_simple exp =
    match exp with
    | Unit1 -> "()"
    | Int1 i -> string_of_int i
    | Var1 (_, name) -> fmt_vname name
    | Lambda1 _ -> "λ..."
    | _ -> "..."
  in
  "{" ^ fmt_t ~nctx (typeof exp) ^ "} " ^ 
  match exp with
  | Unit1  -> "()"
  | Int1 i -> string_of_int i
  | Var1 (_, name) -> fmt_vname name
  | Call1 (_, f, args) ->
      fmt_simple f ^ " " ^ String.concat " " (map fmt_simple args)
  | If1 (_, c, y, n) ->
      "if " ^ fmt_simple c
      ^ " then " ^ fmt_simple y
      ^ " else " ^ fmt_simple n
  | LetRec1 (_, name, value, body) ->
      "let rec " ^ fmt_vname name ^ " = " ^ fmt_simple value
      ^ " in " ^ fmt_simple body
  | Lambda1 (_, ps, body) ->
      "λ" ^ String.concat " " (map fmt_vname ps) ^ " -> " ^ fmt_simple body


let rec hm ?nctx (tctx : vname tctx) (exp : exp0) : exp1 =
  let nctx = ctx_of nctx in
  let hm tctx exp =
    (* print_endline ("reconstructing " ^ fmt_exp0 ~nctx exp); *)
    let result = hm ~nctx tctx exp in
    (* print_endline ("finished reconstructing " ^ fmt_exp1 ~nctx result); *)
    result
  in
  let unify = unify ~nctx in
  let abstract = abstract ~nctx in
  let instantiate = instantiate ~nctx in
  match exp with
  | Unit0 -> Unit1
  | Int0 i -> Int1 i
  | Var0 name ->
      if tctx_mem name tctx 
      then Var1 (instantiate (tctx_get name tctx), name)
      else failwith ("variable " ^ fmt_vname name ^ "out of scope")
  | Call0 (f0, args0) ->
      let return_type = gentvar () in
      let f1    = hm tctx f0 in
      let args1 = map (hm tctx) args0 in
      let f_type = typeof f1 in
      let arg_types = map typeof args1 in
      unify f_type (TArrow (arg_types, return_type));
      Call1 (return_type, f1, args1)
  | If0 (c0, y0, n0) ->
      let c1 = hm tctx c0 in
      let y1 = hm tctx y0 in
      let n1 = hm tctx n0 in
      unify (typeof c1) TBool;
      unify (typeof y1) (typeof n1);
      If1 (typeof y1, c1, y1, n1)
  | LetRec0 (name, value0, body0) ->
      let name_type   = gentvar () in
      let value0_env  = tctx_cons (Term (name, name_type)) tctx in
      let value1_mono = hm value0_env value0 in
      let value1_type = typeof value1_mono in
      unify name_type value1_type;
      let abstract  = abstract value1_type tctx in
      let value1    = map_exp_t (fun _ -> abstract) value1_mono in
      let body0_env = tctx_cons (Term (name, abstract)) tctx in
      let body1     = hm body0_env body0 in
      LetRec1 (typeof body1, name, value1, body1)
  | Lambda0 (ps, body0) ->
      let param_types = map gentvar ps in
      let param_binds = map2 (fun p t -> Term (p, t)) ps param_types in
      let body0_env   = tctx_add_all param_binds tctx in
      let body1       = hm body0_env body0 in
      Lambda1 (TArrow (param_types, typeof body1), ps, body1)
  | Annot0 (exp0, intended_type) ->
      let exp1 = hm tctx exp0 in
      unify (typeof exp1) intended_type;
      exp1

;;
let idnil  = VN ("nil", genid ())
let idsucc = VN ("succ", genid ())
let idnull = VN ("null?", genid ())
let idcons = VN ("cons", genid ())
let idcar  = VN ("car", genid ())
let idcdr  = VN ("cdr", genid ())
let nil    = Var0 idnil
let succ   = Var0 idsucc
let null   = Var0 idnull
let cons   = Var0 idcons
let car    = Var0 idcar
let cdr    = Var0 idcdr
let tsucc = TArrow ([TInt], TInt)
let ida = gentname ()
let idb = gentname ()
let idc = gentname ()
let idd = gentname ()
let ide = gentname ()
let ga = TParam ida
let gb = TParam idb
let gc = TParam idc
let gd = TParam idd
let ge = TParam ide
let tnil  = TUniversal ([ida], TApplied (CN "list", [ga]))
let tnull = TUniversal ([idb], TArrow ([TApplied (CN "list", [gb])], TBool))
let tcons = TUniversal ([idc], TArrow ([gc; TApplied (CN "list", [gc])], TApplied (CN "list", [gc])))
let tcar  = TUniversal ([idd], TArrow ([TApplied (CN "list", [gd])], gd))
let tcdr  = TUniversal ([ide], TArrow ([TApplied (CN "list", [ge])], TApplied (CN "list", [ge])))
let type_env = TCtx [
  Term (idsucc, tsucc);
  Term (idnil, tnil);
  Term (idnull, tnull);
  Term (idcons, tcons);
  Term (idcar, tcar);
  Term (idcdr, tcdr);
]
let idmap  = VN ("mapcar", genid ())
let idf    = VN ("f", genid ())
let idlst  = VN ("lst", genid ())
let mapcar = Var0 idmap
let f      = Var0 idf
let lst    = Var0 idlst
let body   = Lambda0 ([idf; idlst],
               If0 (
                 Call0 (null, [lst]),
                 nil,
                 Call0 (
                   cons, [
                     Call0 (f, [Call0 (car, [lst])]);
                     Call0 (mapcar, [f; Call0 (cdr, [lst])])])))
let program0 = LetRec0 (idmap, body,
                 Call0 (mapcar, [
                   succ;
                   Call0 (cons, [
                     Int0 1;
                     Call0 (cons, [
                       Int0 2;
                       Call0 (cons, [
                         Int0 3;
                         nil])])])]))
;;
print_endline "Reconstructing mapcar";
let nctx = namectx_create () in
let program1 = hm ~nctx type_env program0 in
print_endline ("Inferred type: " ^ fmt_t ~nctx (typeof program1));
print_endline ("Reprinted: " ^ fmt_t (typeof program1))


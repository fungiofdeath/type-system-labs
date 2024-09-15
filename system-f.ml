
open List

let flatmap (f : 'a -> 'b list) (list : 'a list) : 'b list = flatten (map f list)

(******************************************************************************)
(* Important types *)

type vname = VN of string * int
type cname = CN of string
type tname = TN of string option * int
type t =
  | TUnit
  | TInt
  | TVariable  of tvar  ref      (*     'x : (previously-)unknown type *)
  | TConstant  of tname          (*      x : known type, different from all other constants *)
  | TParam     of tname          (*     ?X : parameter to a universal type *)
  | TArrow     of t list * t     (* t -> t : function's type *)
  | TApplied   of cname * t list (*    t c : generic structure type *)
  | TUniversal of tname list * t (*   ∀X.t : polymorphic type -> term function *)
and tvar =
  | Linked  of tname * t         (* this variable has already been unified against *)
  | Unknown of tname             (* this variable is totally unknown *)

type binding =
  | Term of vname * t            (* x:t : x has type t *)
  | Decl of tname                (*   X : X is a generic type *)
type tctx = TCtx of binding list (*   Γ : contains a list of all types bound
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

let basic_fmt_vname (VN (name, id)) = name ^ "_" ^ string_of_int id
let basic_fmt_cname (CN name) = name
let basic_fmt_tname (TN (name_opt, id)) =
  match name_opt with
  | Some s -> s ^ "_" ^ string_of_int id
  | None   ->     "_" ^ string_of_int id
let rec basic_fmt_t (t : t) : string =
  let open String in
  match t with
  | TUnit -> "unit"
  | TInt  -> "int"
  | TVariable { contents = Unknown name  } -> "'" ^ basic_fmt_tname name
  | TVariable { contents = Linked (_, t) } -> "[" ^ basic_fmt_t t ^ "]"
  | TConstant name -> basic_fmt_tname name
  | TParam name -> "?" ^ uppercase_ascii (basic_fmt_tname name)
  | TArrow (doms, cod) ->
      let doms = concat ", " (List.map basic_fmt_t doms) in
      "(" ^ doms ^ ") -> " ^ basic_fmt_t cod
  | TApplied (x, xs) ->
      let args = concat ", " (List.map basic_fmt_t xs) in
      "(" ^ args ^ ") " ^ basic_fmt_cname x
  | TUniversal (qs, inner) ->
      let quantified = concat " " (List.map basic_fmt_tname qs) in
      "∀" ^ uppercase_ascii quantified ^ ". " ^ basic_fmt_t inner

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
  | Linked (name, t) -> failwith (basic_fmt_tname name ^ "is already linked")
  | Unknown name -> tvar := Linked (name, linkto)
let of_tvar (tvar : tvar) : t =
  match tvar with
  | Linked (_, t) -> t
  | Unknown name -> failwith (basic_fmt_tname name ^ " is not linked")

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

let freevars_of_binding (binding : binding) : TNameSet.t =
  match binding with
  | Decl name -> TNameSet.singleton name
  | Term (_, t) -> freevars_of_type t

let freevars_of_tctx (TCtx bindings) : TNameSet.t =
  concat_tname_sets (map freevars_of_binding bindings)

let rec unify (t1 : t) (t2 : t) =
  match t1, t2 with
  | TUnit, TUnit -> ()
  | TInt,  TInt  -> ()
  | TVariable ref, _ when not (is_linked !ref) -> link ref t2
  | TVariable ref, _ when is_linked !ref -> unify t2 (of_tvar !ref)
  | _, TVariable _ -> unify t2 t1
  | TConstant name1, TConstant name2 when name1 = name2 -> ()
  | TArrow (doms1, cod1), TArrow (doms2, cod2) ->
      iter2 unify doms1 doms2;
      unify cod1 cod2
  | TApplied (x, xs), TApplied (y, ys) when x = y -> iter2 unify xs ys
  | _ ->
      failwith (
        "disallowed unification "
        ^ basic_fmt_t t1
        ^ " ~ "
        ^ basic_fmt_t t2
      )

let rec subst (alist : (tname * t) list) (t : t) : t =
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
        failwith (
          "scope error, cannot subst {"
          ^  String.concat ", " (map basic_fmt_tname (Set.to_list errors))
          ^ "} into "
          ^ basic_fmt_t t
        )
      else TUniversal (qs, subst alist inner)
  | _ -> t

let apply (universal : t) (args : t list) =
  match universal with
  | TUniversal (qs, inner) -> subst (combine qs args) inner
  | _ ->
      failwith (
        "tried to apply a non-universal type " ^ basic_fmt_t universal
      )

let instantiate (t : t) =
  match t with
  | TUniversal (qs, inner) ->
      let alist = map (fun q -> q, gentvar ()) qs in
      subst alist inner
  | _ -> t

let abstract (t : t) (ctx : tctx) : t =
  let fv_t   = freevars_of_type t in
  let fv_ctx = freevars_of_tctx ctx in
  let frees  = TNameSet.(diff fv_t fv_ctx |> to_list) in
  let generics = map (fun fv -> (fv, gentparam ())) frees in
  TUniversal (frees, subst generics t)





















(******************************************************************************)
(* Proper pretty printing *)

(* counts the number of generated names *)
(* type tnamectx = TNCtx of ((int * string) list * int) ref
let greek = "αꞵγδεζηθκμστπχφψ" *)

(* let fmt_tname (TNCtx ref) (TN (name_opt, id)) : string =
  let seen, count = !ref in
  match List.assoc_opt id seen with
  | Some s -> s
  | None ->
      match name_opt with
      | Some name -> (
          ref := (id, name)::seen, count;
          name
        )
      | None -> (
          let open String in
          let letter = (length greek) mod count in
          let postindex = (length greek) / count in
          let formatted =
            if postindex != 0
            then make 1 greek.[letter] ^ string_of_int postindex
            else make 1 greek.[letter]
          in
          ref := (id, formatted)::seen, count + 1;
          formatted
        ) *)












exception Todo of string (* not finished *)
exception Lazy of string (* too lazy to handle *)

module type MONOID = sig
  type m
  val mempty : m
  val mcombine : m -> m -> m
end

module Monoid(M: MONOID) = struct
  let combine_all ms = List.fold_left M.mcombine M.mempty ms
end

module Helper = struct
  module type ORDERED = sig
    type comparable
    val compare : comparable -> comparable -> int
  end
  module Minimal(O: ORDERED) = struct
    module Map = Map.Make(
      struct
        type t = O.comparable
        let compare = O.compare
      end
    )
    module Set = Set.Make(
      struct
        type t = O.comparable
        let compare = O.compare
      end
    )
  end
  module Make(O: ORDERED) = struct
    type t = O.comparable
    module Private_ = Minimal(O)
    module Set = struct
      include Private_.Set
      include Monoid(
        struct
          type m = t
          let mempty = empty
          let mcombine = union
        end
      )
      let to_list set = List.of_seq (to_seq set)
      let to_map (f: O.comparable -> O.comparable * 'a) set =
        Private_.Map.of_seq (Seq.map f (to_seq set))
    end
    module Map = struct
      include Private_.Map
      let to_list map = List.of_seq (to_seq map)
      let to_set map = Set.of_seq (Seq.map (fun (k, _) -> k) (to_seq map))
      let map_keys f map = of_seq (Seq.map (fun (k, v) -> (f k, v)) (to_seq map))
      let map_to_set (f : O.comparable -> O.comparable) map =
        Set.of_seq (Seq.map (fun (k, _) -> f k) (to_seq map))
      let map_to_list (f : O.comparable -> 'a -> 'b) map =
        List.of_seq (Seq.map (fun (k, v) -> f k v) (to_seq map))
      let map_keys_to_list (f : O.comparable -> 'a) map =
        List.of_seq (Seq.map (fun (k, _) -> f k) (to_seq map))
      let map_values_to_list f map = List.of_seq (Seq.map (fun (_, v) -> f v) (to_seq map))
    end
  end
end

type typname = int
module TypnameHelper = Helper.Make(
  struct
    type comparable = typname
    let compare x y = x - y
  end
)

type typ =
  | TUnit | TInt | TString | TBool
  | TVar of typname
  | TCon of typname * typ list
  | Poly of TypnameHelper.Set.t * typ

type varname = int
module VarnameHelper = Helper.Make(
  struct
    type comparable = varname
    let compare x y = x - y
  end
)

type obj =
  | OUnit
  | OInt of int
  | OString of string
  | OBool of bool
  | OFunc of env * varname list * expression
and env = obj VarnameHelper.Map.t
and expression =
  | Literal of obj
  | Var of varname
  | Call of expression * expression list
  | If of expression * expression * expression
  | Let of varname * expression * expression
  | Func of varname list * expression
  | Annot of typ * expression


let genid =
  let count = ref 0 in
  fun () ->
    let saved = !count in
    count := !count + 1;
    saved
let genvar  () =  Var (genid ())
let gentvar () = TVar (genid ())

module Types = struct
  open List
  module Set = TypnameHelper.Set
  module Map = TypnameHelper.Map

  let combine_children combine f typ =
    match typ with
    | TCon (_, children) -> combine (map f children)
    | Poly (_, mono) -> combine [f mono]
    | _ -> combine []

  let replace_children f typ =
    match typ with
    | TCon (name, children) -> TCon (name, map f children)
    | Poly (binds, mono) -> Poly (binds, f mono)
    | _ -> typ
  
  let rec subst_vars assoc typ =
    let typ = replace_children (subst_vars assoc) typ in
    match typ with
    | TVar n -> (
      match assoc_opt n assoc with
      | None -> typ
      | Some found -> found
      )
    | _ -> typ

  let rec free_vars typ =
    let open Set in
    let combine = fold_left union empty in
    match typ with
    | TVar n -> singleton n
    | Poly (binds, mono) ->
      diff (free_vars mono) binds
    | _ -> combine_children combine free_vars typ

  let instantiate typ =
    match typ with
    | Poly (binds, mono) ->
      let binds = Set.to_list binds in
      let new_types = map (fun id -> (id, gentvar ())) binds in
      subst_vars new_types mono
    | _ -> typ
end

module Exprs = struct
  open List
  module Set = VarnameHelper.Set
  module Map = VarnameHelper.Map

  let combine_children combine f typ =
    match typ with
    | Call (func, args) -> combine (f func :: map f args)
    | If (c, y, n) -> combine [f c; f y; f n]
    | Let (_, init_value, body) -> combine [f init_value; f body]
    | Func (_, body) -> combine [f body]
    | Annot (_, e) -> combine [f e]
    | _ -> combine []

  let replace_children f expr =
    match expr with
    | Call (func, args) -> Call (f func, map f args)
    | If (c, y, n) -> If (f c, f y, f n)
    | Let (name, init_value, body) -> Let (name, f init_value, f body)
    | Func (params, body) -> Func (params, f body)
    | Annot (typ, e) -> Annot (typ, f e)
    | _ -> expr

  let rec subst_vars assoc expr =
    let expr = replace_children (subst_vars assoc) expr in
    match expr with
    | Var n -> (
      match assoc_opt n assoc with
      | None -> expr
      | Some found -> found
      )
    | _ -> expr

  let rec free_vars expr =
    let open Set in
    let combine = fold_left union empty in
    match expr with
    | Var n -> singleton n
    | Func (ps, body) ->
      let ps = of_list ps in
      diff (free_vars body) ps
    | Let (name, init_value, body) ->
      let value_frees = free_vars init_value in
      let body_frees = remove name (free_vars body) in
      union value_frees body_frees
    | _ -> combine_children combine free_vars expr

  let rec ensure_fully_annotated expr =
    match expr with
    | Annot (typ, inner) -> Annot (typ, replace_children ensure_fully_annotated inner)
    | _ -> Annot (gentvar (), replace_children ensure_fully_annotated expr)
end

module TypeSystem = struct
  open List
  type tenv = typ Types.Map.t
  
  let map_tenv_types f tenv = Types.Map.map_values_to_list f tenv

  let abstract tenv typ =
    let open Types.Set in
    let bound_vars = combine_all (map_tenv_types Types.free_vars tenv) in
    Poly (diff (Types.free_vars typ) bound_vars, typ)
end


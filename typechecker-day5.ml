(* totally untested -- im sure it works fine :clueless: *)

open List

(* small utils for combining options and lists *)

(* :: for optional items *)
let ( **<? ) (opt : 'a option) (items : 'a list) : 'a list =
  match opt with
  | Some item -> item :: items
  | None      -> items

(* reverse :: for optional items *)
let ( >**? ) (items : 'a list) (opt : 'a option) : 'a list =
  match opt with
  | Some item -> items @ [item]
  | None      -> items

(* filter all Some cases into a list *)
let filter_options (opt_items : 'a option list) : 'a list =
  flatten (map Option.to_list opt_items)



type type_id          = TypeId of string option * int
type type_constructor = TypeConstructor of string option * int
type monotype =
  | TConstant of type_id                          (* nominal types *)
  | TGeneric  of type_id                          (* parameters to polytypes *)
  | TVariable of type_var ref                     (* unknown types *)
  | TArrow    of monotype list * monotype         (* function types*)
  | TApplied  of type_constructor * monotype list (* type constructors *)
and type_var = Unknown of type_id | Known of monotype
type polytype =
  | Mono of monotype                              (* concrete types*)
  | Poly of type_id list * monotype               (* polymorphic types *)

type var_id = VarId of string option * int
type exp0 = (* untyped ast *)
  | Unit0
  | Int0    of int
  | Var0    of var_id
  | Call0   of exp0 * exp0 list
  | If0     of exp0 * exp0 * exp0
  | LetRec0 of var_id * exp0 * exp0
  | Lambda0 of var_id list * exp0
  | Annot0  of monotype * exp0

type type_env = (var_id * polytype) list

type exp1 = (* typed ast *)
  | Unit1
  | Int1    of int
  | Var1    of monotype * var_id
  | Call1   of monotype * exp1 * exp1 list
  | If1     of monotype * exp1 * exp1 * exp1
  | LetRec1 of monotype * var_id * exp1 * exp1
  | Lambda1 of monotype * var_id list * exp1
  (* drop annotation nodes since all nodes are annotated *)

type error_tree =
  | Single of string
  | Nested of string * error_tree list

exception AlreadyLinked

(* just used to get unique ids*)
let timestamp : int ref = ref (-1) (* pre-incremented *)
let gettime () = incr timestamp; !timestamp

(* helpful constructors *)
let constant ?(name = None) () = TConstant (TypeId (name, gettime ()))
let unknown ?(name = None) () = TVariable (ref (Unknown (TypeId (name, gettime ()))))
let generic ?(name = None) () = TGeneric (TypeId (name, gettime ()))
let constructor ?(name = None) () = TypeConstructor (name, gettime ())

(* unify a typevar against a monotype *)
let link (TVariable ref) monotype =
  match !ref with
  | Known _ -> raise AlreadyLinked
  | _ -> ref := Known monotype

(*
 * important built-in types
 * c = type constructor
 * t = type
 *)
let t_error = constant ~name:(Some "error") ()
let t_unit = constant ~name:(Some "unit") ()
let t_int = constant ~name:(Some "int") ()
let t_bool = constant ~name:(Some "bool") ()
let c_list = constructor ~name:(Some "list") ()

(*
 * convert stuff to strings
 * should be called fmt_* but whatever
 *)
let print_id (TypeId (name, id)) =
  match name with
  | None -> "_" ^ string_of_int id
  | Some name -> name ^ "_" ^ string_of_int id
let print_constructor (TypeConstructor (name, id)) =
  match name with
  | None -> "_" ^ string_of_int id
  | Some name -> name ^ "_" ^ string_of_int id
let print_variable (VarId (name, id)) =
  match name with
  | None -> "_" ^ string_of_int id
  | Some name -> name ^ "_" ^ string_of_int id
let rec print_monotype (monotype : monotype) : string =
  let comma x y = x ^ ", " ^ y in
  match monotype with
  | TConstant id -> print_id id
  | TGeneric id -> "'" ^ print_id id
  | TVariable { contents = Unknown id } -> "?" ^ print_id id
  | TVariable { contents = Known monotype } -> print_monotype monotype
  | TArrow (doms, cod) ->
      let domains = map print_monotype doms |> fold_left comma "" in
      "(" ^ domains ^ ") -> " ^ print_monotype cod
  | TApplied (con, xs) ->
      let args = map print_monotype xs |> fold_left comma "" in
      print_constructor con ^ "(" ^ args ^ ")"
let rec print_error ?(indentation = "") (error_tree : error_tree) : string =
  let print_child child =
    let increased = indentation ^ " " in
    "\n" ^ print_error ~indentation:increased child
  in
  match error_tree with
  | Single err -> indentation ^ err
  | Nested (parent, children) ->
      let child_errors = map print_child children |> fold_left ( ^ ) "" in
      indentation ^ parent ^ ":" ^ child_errors

(* guard a possibly non-empty list of errors *)
let catch desc errors = if length errors = 0 then None else Some (Nested (desc, errors))

(* helper just to read off a exp1's type *)
let typeof exp =
  match exp with
  | Unit1                -> t_unit
  | Int1 _               -> t_int
  | Var1 (t, _)          -> t
  | Call1 (t, _, _)      -> t
  | If1 (t, _, _, _)     -> t
  | LetRec1 (t, _, _, _) -> t
  | Lambda1 (t, _, _)    -> t

let rec unify (t1 : monotype) (t2 : monotype) : error_tree option =
  let anded () = print_monotype t1 ^ " and " ^ print_monotype t2 in
  let mismatch () = Some (Single (anded () ^ " do not match")) in
  let incompatible () =
    Some (Single ("types " ^ anded () ^ " are incompatible"))
  in
  let inner errors =
    Some (Nested ("errors occurred while unifying " ^ anded (), errors))
  in
  let recur_pairs xs ys =
    combine xs ys |> map (fun (t1, t2) -> unify t1 t2) |> filter_options
  in
  match t1, t2 with
  | TConstant id1, TConstant id2 when id1 = id2 -> None
  | TConstant _, TConstant _ -> incompatible ()
  | TVariable { contents = Known t1 }, _ -> unify t1 t2
  | TVariable ref, _ -> link t1 t2; None
  | _, TVariable _ -> unify t2 t1
  | TArrow (doms1, cod1), TArrow (doms2, cod2) ->
      recur_pairs doms1 doms2 >**? unify cod1 cod2 |> inner
  | TApplied (c1, xs), TApplied (c2, ys) when c1 = c2 ->
      recur_pairs xs ys |> inner
  | _, _ -> mismatch ()

let inst (poly : polytype) : monotype =
  let rec replace_generics generics mono =
    let recur = replace_generics generics in
    match mono with
    | TConstant _   -> mono
    | TGeneric  id  -> if mem id generics then unknown () else failwith "unexpected generic"
    | TVariable ref -> (
        match !ref with
        | Known kt -> recur kt
        | Unknown id -> mono
      )
    | TArrow (doms, cod) -> TArrow (map recur doms, recur cod)
    | TApplied (id, xs)  -> TApplied (id, map recur xs)
  in
  match poly with
  | Mono mono -> mono
  | Poly ([], mono) -> mono
  | Poly (xs, mono) -> replace_generics xs mono

let abstract (monotype : monotype) (type_env : type_env) : polytype =
  let open struct
    module Set = Set.Make(
      struct
        type t = type_id
        let compare (TypeId (_, id1)) (TypeId (_, id2)) = id1 - id2
      end
    )
  end in
  let flatmap f list = flatten (map f list) in
  let rec fvlist monos = flatmap fv monos
  and fv monotype =
    match monotype with
    | TConstant id -> [id]
    | TGeneric  id -> failwith "generics should not exist here"
    | TVariable { contents = Known sub  } -> fv sub
    | TVariable { contents = Unknown id } -> [id]
    | TArrow (doms, cod) -> fvlist doms @ fv cod
    | TApplied (_, xs) -> fvlist xs
  in
  let fvs_tyenv  =
    let fv_bind (_, polytype) =
      match polytype with
      | Mono monotype -> fv monotype
      | Poly (_, monotype) -> fv monotype
    in Set.of_list (flatmap fv_bind type_env)
  in
  let fvs_mono = Set.of_list (fv monotype) in
  let generics_mem = Set.diff fvs_mono fvs_tyenv in
  let generics_lst = Set.to_list generics_mem in
  if length generics_lst != 0 then
    let zipped =
      map (fun (TypeId (name, _)) -> generic ~name:name ()) generics_lst
      |> combine generics_lst
    in
    let get id = assoc id zipped in
    let replaced =
      let rec walk monotype =
        match monotype with
        | TConstant id when Set.mem id generics_mem -> get id
        | TConstant _ -> monotype
        | TVariable { contents = Unknown id } when Set.mem id generics_mem -> get id
        | TVariable _ -> monotype
        | TGeneric _ -> failwith "generics should not exist here (x2)"
        | TArrow (doms, cod) -> TArrow (map walk doms, walk cod)
        | TApplied (cid, xs) -> TApplied (cid, map walk xs)
      in
      walk monotype
    in Poly (generics_lst, replaced)
  else Mono monotype

let rec reconstruct (exp : exp0) (type_env : type_env) : exp1 * error_tree option =
  match exp with
  | Unit0 -> Unit1, None
  | Int0 i -> Int1 i, None
  | Var0 id -> (
      match assoc_opt id type_env with
      | Some poly -> Var1 (inst poly, id), None
      | None -> Var1 (t_error, id), Some (Single ("variable " ^ print_variable id))
    )
  | Call0 (func, args) ->
      let ty_r = unknown ~name:(Some "fr") () in
      let func1, ferr  = reconstruct func type_env in
      let args1, aerrs = split (map (fun a -> reconstruct a type_env) args) in
      let uerrs = unify (typeof func1) (TArrow (map typeof args1, ty_r)) in
      let errors = uerrs **<? ferr **<? filter_options aerrs in
      Call1 (ty_r, func1, args1), catch "error while reconstructing call" errors
  | If0 (cexp, yexp, nexp) ->
      let cexp1, cerr = reconstruct cexp type_env in
      let yexp1, yerr = reconstruct yexp type_env in
      let nexp1, nerr = reconstruct nexp type_env in
      let cuerrs = unify (typeof cexp1) t_bool in
      let ynuerrs = unify (typeof yexp1) (typeof nexp1) in
      let errors = cuerrs **<? ynuerrs **<? cerr **<? yerr **<? nerr **<? [] in
      If1 (typeof yexp1, cexp1, yexp1, nexp1), catch "error while reconstructing if" errors
  | LetRec0 (name, value, body) ->
      let ty_v = unknown ~name:(Some "lv") () in
      let venv = (name, Mono ty_v)::type_env in
      let value1, verr = reconstruct value venv in
      let benv = (name, abstract ty_v type_env)::type_env in
      let body1, berr = reconstruct body benv in
      let errors = verr **<? berr **<? [] in
      LetRec1 (typeof body1, name, value1, body1), catch "error while reconstructing let" errors
  | Lambda0 (ps, body) ->
      let tys_ps = map (fun id -> unknown ~name:(Some (print_variable id)) ()) ps in
      let benv = (map (fun t -> Mono t) tys_ps |> combine ps) @ type_env in
      let body1, berr = reconstruct body benv in
      let errors = Option.to_list berr in
      Lambda1 (TArrow (tys_ps, typeof body1), ps, body1), catch "error while reconstructing lambda" errors
  | Annot0 (ty_a, e) ->
      let e1, err = reconstruct e type_env in
      let ty_e = typeof e1 in
      let uerr = unify ty_e ty_a in
      let errors = uerr **<? err **<? [] in
      let msg = "incorrect annotation. expected " ^ print_monotype ty_a ^ " got " ^ print_monotype ty_e in
      e1, catch msg errors

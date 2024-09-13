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

let reduce f init list =
  match list with
  | [] -> init
  | x::[] -> x
  | x::y::zs -> fold_left f (f x y) zs

let intersperse ?(sep = ", ") strings =
  let middle x y = x ^ sep ^ y in
  reduce middle "" strings

let log_depth = ref ""
let log string = print_endline (!log_depth ^ string)
let enter () = log_depth := !log_depth ^ "  "
let leave_after x =
  log_depth := String.(sub !log_depth 2 (length !log_depth - 2));
  x
let nested f = fun x -> enter (); leave_after (f x)
let log_context string k = log string; enter (); leave_after (k string)

let ( let= ) f k = f k

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
let var ?(name = None) () = VarId (name, gettime ())

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
  (* | Some name -> name ^ "_" ^ string_of_int id *)
  | Some name -> name
let print_constructor (TypeConstructor (name, id)) =
  match name with
  | None -> "_" ^ string_of_int id
  (* | Some name -> name ^ "_" ^ string_of_int id *)
  | Some name -> name
let print_variable (VarId (name, id)) =
  match name with
  | None -> "_" ^ string_of_int id
  (* | Some name -> name ^ "_" ^ string_of_int id *)
  | Some name -> name
let rec print_monotype (monotype : monotype) : string =
  match monotype with
  | TConstant id -> "" ^ print_id id
  | TGeneric id -> "'" ^ print_id id
  | TVariable { contents = Unknown id } -> "?" ^ print_id id
  | TVariable { contents = Known monotype } -> "" ^ print_monotype monotype ^ ""
  | TArrow (doms, cod) ->
      let domains = map print_monotype doms |> intersperse in
      let codomain = " -> " ^ print_monotype cod in (
        match doms with
        | [TArrow _] -> "(" ^ domains ^ ")" ^ codomain
        | [_]        ->       domains       ^ codomain
        |  _         -> "(" ^ domains ^ ")" ^ codomain
      )
  | TApplied (con, xs) ->
      let args = map print_monotype xs |> intersperse in
      let name = print_constructor con in
      if length xs == 1 then args ^ " " ^ name else "(" ^ args ^ ") " ^ name
let print_polytype (polytype : polytype) : string =
  match polytype with
  | Mono monotype -> print_monotype monotype
  | Poly (generics, monotype) ->
      "∀{" ^ intersperse (map print_id generics) ^ "}. "
      ^ print_monotype monotype
let print_type_env ?(indentation = "") type_env =
  let rec inner rest =
    match rest with
    | [] -> ""
    | (var, poly)::rest ->
        "\n " ^ indentation ^ print_variable var ^ ": " ^ print_polytype poly
        ^ inner rest
  in
  match type_env with
  | []   -> "{}"
  | rest -> "{" ^ inner rest ^ indentation ^ "\n" ^ indentation ^ "}"
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
    if length errors = 0
    then None
    else Some (Nested ("errors occurred while unifying " ^ anded (), errors))
  in
  let recur_pairs xs ys =
    combine xs ys |> map (fun (t1, t2) -> unify t1 t2) |> filter_options
  in
  let= _ = log_context ("unify " ^ anded ()) in
  match t1, t2 with
  | _, _ when t1 == t2 -> None
  | TConstant id1, TConstant id2 when id1 = id2 -> None
  | TConstant _, TConstant _ -> incompatible ()
  | TVariable r1, TVariable r2 when r1 == r2 -> None
  | TVariable { contents = Known t1 }, _ -> unify t1 t2
  | TVariable ref, _ ->
      let saved = print_monotype t1 in
      link t1 t2;
      log ("linking " ^ saved ^ " := " ^ print_monotype t1);
      None
  | _, TVariable _ -> unify t2 t1
  | TArrow (doms1, cod1), TArrow (doms2, cod2) ->
      (recur_pairs doms1 doms2 >**? unify cod1 cod2) |> inner
  | TApplied (c1, xs), TApplied (c2, ys) when c1 = c2 ->
      recur_pairs xs ys |> inner
  | _, _ -> mismatch ()

let map_id f (TypeId (name, id)) = TypeId (name, f id)
let new_id = map_id (fun _ -> gettime ())

let inst (poly : polytype) : monotype =
  let= _ = log_context ("instantiating " ^ print_polytype poly) in
  let rec replace_generics generics mono =
    let= _ = log_context ("inst " ^ print_monotype mono) in
    let recur = replace_generics generics in
    match mono with
    | TConstant _   -> mono
    | TGeneric id  -> (
        match assoc_opt id generics with
        | Some found -> found
        | None -> failwith ("unexpected generic" ^ print_id id)
      )
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
  | Poly (xs, mono) ->
      let generic id = TVariable (ref (Unknown (new_id id))) in
      let mapping = combine xs (map generic xs) in
      replace_generics mapping mono

let abstract (monotype : monotype) (type_env : type_env) : polytype =
  let module Set = Set.Make(
    struct
      type t = type_id
      let compare (TypeId (_, id1)) (TypeId (_, id2)) = id1 - id2
    end
  )
  in
  log ("abstract " ^ print_monotype monotype);
  let= _ = log_context ("type env is " ^ print_type_env ~indentation:!log_depth type_env) in
  let flatmap f list = flatten (map f list) in
  let rec fvlist monos = flatmap fv monos
  and fv monotype =
    let= _ = log_context ("fv " ^ print_monotype monotype) in
    match monotype with
    | TConstant id -> [id]
    | TGeneric  id -> []
    | TVariable { contents = Known sub  } -> fv sub
    | TVariable { contents = Unknown id } -> [id]
    | TArrow (doms, cod) -> fvlist doms @ fv cod
    | TApplied (_, xs) -> fvlist xs
  in
  let fvs_tyenv  =
    let fv_bind (var, polytype) =
      let= _ = log_context ("env " ^ print_variable var ^ ": " ^ print_polytype polytype) in
      match polytype with
      | Mono monotype -> fv monotype
      | Poly (_, monotype) -> fv monotype
    in Set.of_list (flatmap fv_bind type_env)
  in
  let fvs_mono = Set.of_list (fv monotype) in
  let generics_mem = Set.diff fvs_mono fvs_tyenv in
  let generics_lst = Set.to_list generics_mem in
  log ("resulting generics: " ^ intersperse (map print_id generics_lst));
  if length generics_lst != 0 then
    let= _ = log_context "polytype" in
    let new_generic (TypeId (name, _)) =
      let TGeneric id = generic ~name:name () in
      id
    in
    let new_generics = map new_generic generics_lst in
    let zipped = combine generics_lst new_generics in
    log (
      "to be replaced: ["
      ^ intersperse (
          map (fun (id, to_id) -> print_id id ^ ": " ^ print_id to_id) zipped
        )
      ^ "]");
    let get id = assoc id zipped in
    let replaced =
      let rec walk monotype : monotype =
        let= _ = log_context ("replacing generics in " ^ print_monotype monotype) in
        match monotype with
        | TConstant id when Set.mem id generics_mem -> TGeneric (get id)
        | TConstant _ -> monotype
        | TVariable { contents = Unknown id } when Set.mem id generics_mem ->
            log ("found " ^ print_id id);
            TGeneric (get id)
        | TVariable { contents = Known monotype } -> walk monotype
        | TVariable _ -> monotype
        | TGeneric _ -> failwith "generics should not exist here"
        | TArrow (doms, cod) -> TArrow (map walk doms, walk cod)
        | TApplied (cid, xs) -> TApplied (cid, map walk xs)
      in
      walk monotype
    in
    let polytype = Poly (new_generics, replaced) in
    log ("abstraction = " ^ print_polytype polytype);
    polytype
  else (
    log ("abstraction = " ^ print_monotype monotype);
    Mono monotype
  )

let rec reconstruct (exp : exp0) (type_env : type_env) : exp1 * error_tree option =
  match exp with
  | Unit0   -> log "reconstructing ()"; Unit1, None
  | Int0 i  -> log "reconstructing int"; Int1 i, None
  | Var0 id -> (
      let= _ = log_context ("reconstructing variable " ^ print_variable id) in
      match assoc_opt id type_env with
      | Some poly ->
          let instantiated = inst poly in
          log ("instantied " ^ print_monotype instantiated);
          Var1 (instantiated, id), None
      | None -> Var1 (t_error, id), Some (Single ("variable " ^ print_variable id))
    )
  | Call0 (func, args) ->
      let= _ = log_context "reconstructing call" in
      let ty_r = unknown ~name:(Some "fr") () in
      log ("intro " ^ print_monotype ty_r);
      let func1, ferr  = reconstruct func type_env in
      let args1, aerrs = split (map (fun a -> reconstruct a type_env) args) in
      let uerrs = unify (typeof func1) (TArrow (map typeof args1, ty_r)) in
      log ("function " ^ print_monotype (typeof func1));
      log ("result " ^ print_monotype ty_r);
      let errors = uerrs **<? ferr **<? filter_options aerrs in
      Call1 (ty_r, func1, args1), catch "error while reconstructing call" errors
  | If0 (cexp, yexp, nexp) ->
      log "reconstructing if";
      enter ();
      let cexp1, cerr = reconstruct cexp type_env in
      leave_after ();
      log "then";
      enter ();
      let yexp1, yerr = reconstruct yexp type_env in
      leave_after ();
      log "else";
      enter ();
      let nexp1, nerr = reconstruct nexp type_env in
      leave_after ();
      let= _ = log_context "if/finally" in
      let cuerrs = unify (typeof cexp1) t_bool in
      let ynuerrs = unify (typeof yexp1) (typeof nexp1) in
      let errors = cuerrs **<? ynuerrs **<? cerr **<? yerr **<? nerr **<? [] in
      If1 (typeof yexp1, cexp1, yexp1, nexp1), catch "error while reconstructing if" errors
  | LetRec0 (name, value, body) ->
      log ("reconstructing let rec " ^ print_variable name ^ " = ");
      enter ();
      let ty_v = unknown ~name:(Some "lv") () in
      let venv = (name, Mono ty_v)::type_env in
      log ("value type env is " ^ print_type_env ~indentation:!log_depth venv);
      let value1, verr = reconstruct value venv in
      let uerr = unify ty_v (typeof value1) in
      leave_after ();
      log "let abstracting";
      enter ();
      let ty_abstract = abstract ty_v type_env in
      let benv = (name, ty_abstract)::type_env in
      leave_after ();
      let= _ = log_context ("body type env is " ^ print_type_env ~indentation:!log_depth benv) in
      let body1, berr = reconstruct body benv in
      let errors = verr **<? uerr **<? berr **<? [] in
      LetRec1 (typeof body1, name, value1, body1), catch "error while reconstructing let" errors
  | Lambda0 (ps, body) ->
      let= _ =
        log_context
          ("reconstructing λ" ^ intersperse (map print_variable ps) ^ " ->")
      in
      let tys_ps = map (fun id -> unknown ~name:(Some (print_variable id)) ()) ps in
      let new_types = map (fun t -> Mono t) tys_ps |> combine ps in
      iter (fun (id, poly) ->
              log ("param " ^ print_variable id ^ ": " ^ print_polytype poly))
        new_types;
      let benv =  new_types @ type_env in
      let body1, berr = reconstruct body benv in
      let errors = Option.to_list berr in
      Lambda1 (TArrow (tys_ps, typeof body1), ps, body1), catch "error while reconstructing lambda" errors
  | Annot0 (ty_a, e) ->
      let= _ = log_context ("reconstructing annotation " ^ print_monotype ty_a) in
      let e1, err = reconstruct e type_env in
      let ty_e = typeof e1 in
      let uerr = unify ty_e ty_a in
      let errors = uerr **<? err **<? [] in
      let msg = "incorrect annotation. expected " ^ print_monotype ty_a ^ " got " ^ print_monotype ty_e in
      e1, catch msg errors

let idnil  = var ~name:(Some "nil") ()
let idsucc = var ~name:(Some "succ") ()
let idnull = var ~name:(Some "null?") ()
let idcons = var ~name:(Some "cons") ()
let idcar  = var ~name:(Some "car") ()
let idcdr  = var ~name:(Some "cdr") ()
let nil    = Var0 idnil
let succ   = Var0 idsucc
let null   = Var0 idnull
let cons   = Var0 idcons
let car    = Var0 idcar
let cdr    = Var0 idcdr

let tsucc = Mono (TArrow ([t_int], t_int))
let ga = generic ~name:(Some "α") ()
let gb = generic ~name:(Some "β") ()
let gc = generic ~name:(Some "γ") ()
let gd = generic ~name:(Some "δ") ()
let ge = generic ~name:(Some "ε") ()
let TGeneric id_ = ga
let TGeneric ida = gb
let TGeneric idb = gc
let TGeneric idc = gd
let TGeneric idd = ge
let tnil  = Poly ([id_], TApplied (c_list, [ga]))
let tnull = Poly ([ida], TArrow ([TApplied (c_list, [gb])], t_bool))
let tcons = Poly ([idb], TArrow ([gc; TApplied (c_list, [gc])], TApplied (c_list, [gc])))
let tcar  = Poly ([idc], TArrow ([TApplied (c_list, [gd])], gd))
let tcdr  = Poly ([idd], TArrow ([TApplied (c_list, [ge])], TApplied (c_list, [ge])))

let type_env : type_env = [
  (idsucc, tsucc);
  (idnil, tnil);
  (idnull, tnull);
  (idcons, tcons);
  (idcar, tcar);
  (idcdr, tcdr);
]

let idmap  = var ~name:(Some "mapcar") ()
let idf    = var ~name:(Some "f") ()
let idlst  = var ~name:(Some "lst") ()
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
let program = LetRec0 (idmap, body,
                Call0 (mapcar, [
                  succ;
                  Call0 (cons, [
                    Int0 1;
                    Call0 (cons, [
                      Int0 2;
                      Call0 (cons, [
                        Int0 3;
                        nil])])])]))

(* let idf  = var ~name:(Some "f") ()
let idg  = var ~name:(Some "g") ()
let id_1 = var ()
let id_2 = var ()
let idx  = var ~name:(Some "x") ()
let ef  = Var0 idf
let eg  = Var0 idg
let e_1 = Var0 id_1
let e_2 = Var0 id_2
let ex  = Var0 idx

let program =
  LetRec0 (
    idf,
    Lambda0 ([id_1],
      Call0 (
        Lambda0 ([idg], Call0 (eg, [Unit0])),
        [
          Lambda0 ([id_2], Int0 1)
        ])),
    LetRec0 (
      idx,
      Call0 (ef, [Unit0]),
      ex)) *)
;;
log "-------- start --------";
;;

let reconstructed, err = reconstruct program type_env
let LetRec1 (finaltype, _, newmapcar, _) = reconstructed

;;
log ("inferred program type: " ^ print_monotype finaltype);
log ("inferred mapcar type: " ^ print_monotype (typeof newmapcar));
match err with
| None     -> ()
| Some err -> print_endline ("errors:\n" ^ (print_error err))

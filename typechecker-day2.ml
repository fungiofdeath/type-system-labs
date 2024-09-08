exception Todo                (* not finished *)
exception Lazy of string      (* too lazy to handle *)
exception Invariant of string (* some invariant violated *)
let todo _ = raise Todo

open Format
let rec print_list sep f list =
  match list with
  | [] -> ()
  | x::[] -> f x
  | x::xs -> f x; sep (); print_list sep f xs

exception Too_short
let splitlast xs =
  let q = Queue.create () in
  let rec iter xs =
    match xs with
    | [] -> raise Too_short
    | x::[] -> x
    | x::ys -> Queue.add x q; iter ys
  in
  let last = iter xs in
  List.of_seq (Queue.to_seq q), last

let split3 list =
  let aq = Queue.create () in
  let bq = Queue.create () in
  let cq = Queue.create () in
  List.iter
    (fun (a, b, c) ->
      Queue.add a aq;
      Queue.add b bq;
      Queue.add c cq)
    list;
  List.of_seq (Queue.to_seq aq),
  List.of_seq (Queue.to_seq bq),
  List.of_seq (Queue.to_seq cq)

let zipmap f xs =
  let zipped  = Queue.create () in
  let results = Queue.create () in
  List.iter (fun x ->
              let result = f x in
              Queue.add (x, result) zipped;
              Queue.add result results)
            xs;
  List.of_seq (Queue.to_seq zipped),
  List.of_seq (Queue.to_seq results)

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
      let find_or key otherwise map =
        match find_opt key map with
        | Some t -> t
        | None -> otherwise
      let add_all map list =
        List.fold_left (fun m (k, v) -> add k v m) map list
      let of_list list = of_seq (List.to_seq list)
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

module Ids = struct
  let eid     = 0
  let tunit   = 1
  let tbool   = 2
  let tstring = 3
  let tint    = 4
  let tfun    = 5
end

type typ =
  | TCon of typname
  | TVar of typname
  | TApp of typname * (typ list)
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
  (* numbers below this are for my own use *)
  let count = ref 1000 in
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

  let rec print_type typ =
    let type_name n =
      if n == Ids.tunit   then "unit" else
      if n == Ids.tint    then "int"  else
      if n == Ids.tbool   then "bool" else
      if n == Ids.tstring then "string" else
      if n == Ids.tfun    then "fn" else
      string_of_int n
    in
    match typ with
    | TCon n -> printf "$t_%s" (type_name n)
    | TVar n -> printf "'t_%s" (type_name n)
    | TApp (n, xs) ->
      if n == Ids.tfun
      then
        let butlast, last = splitlast xs in
        printf "fn(";
        print_list (fun () -> printf ", ") print_type butlast;
        printf ") -> ";
        print_type last
      else (
        printf "%s(" (type_name n);
        print_list (fun () -> printf ", ") print_type xs;
        printf ")"
      )
    | Poly (binds, mono) ->
      printf "for {";
      print_list (fun () -> printf ", ") print_int (Set.to_list binds);
      printf "}. ";
      print_type mono

  let combine_children combine f typ =
    match typ with
    | TApp (_, children) -> combine (map f children)
    | Poly (_, mono) -> combine [f mono]
    | _ -> combine []

  let replace_children f typ =
    match typ with
    | TApp (name, children) -> TApp (name, map f children)
    | Poly (binds, mono) -> Poly (binds, f mono)
    | _ -> typ
  
  let rec subst_vars sub typ =
    let typ = replace_children (subst_vars sub) typ in
    match typ with
    | TCon n -> Map.find_or n typ sub
    | TVar n -> Map.find_or n typ sub
    | _ -> typ

  let rec free_vars typ =
    let open Set in
    let combine = fold_left union empty in
    match typ with
    | TCon n -> singleton n
    | TVar n -> singleton n
    | Poly (binds, mono) ->
      diff (free_vars mono) binds
    | _ -> combine_children combine free_vars typ

  let instantiate typ =
    match typ with
    | Poly (binds, mono) ->
      let binds = Set.to_list binds in
      let new_types = Map.of_list (map (fun id -> (id, gentvar ())) binds) in
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

  let rec print_exp exp =
    let print_name name = printf "x_%d" name in
    let print_careful exp =
      match exp with
      | Literal _ | Var _ -> print_exp exp
      | _ -> printf "(@["; print_exp exp; printf "@])"
    in
    let print_obj lit =
      match lit with
      | OUnit -> printf "()"
      | OInt n -> printf "%d" n
      | OBool b -> printf "%b" b
      | OString s -> printf "%s" s
      | OFunc _ -> printf "<closure>"
    in
    match exp with
    | Literal l -> print_obj l
    | Var n -> print_name n
    | Call (f, args) ->
      printf "@[<hv>@[";
      print_exp f;
      printf "@]@ @[";
      print_list (fun () -> printf "@]@ @[") print_careful args;
      printf "@]@]"

    | If (c, y, n) ->
      printf "@[<hv>@[if@;<1 2>@[";
      print_exp c;
      printf "@]@]@ @[then@;<1 2>@[";
      print_exp y;
      printf "@]@]@ @[else@;<1 2>@[";
      print_exp n;
      printf "@]@]@]"

    | Let (name, init_value, body) ->
      printf "let@ ";
      print_name name;
      printf "@ :=@;<1 2>@[";
      print_exp init_value;
      printf "@,in@;<1 2>@[";
      print_exp body;
      printf "@]"

    | Func (params, body) ->
      printf "@[<hv>@[\\@[";
      print_list (fun () -> printf "@ ") print_name params;
      printf "@]@]@;<1 0>=>@]@;<1 2>@[<hov>";
      print_exp body;
      printf "@]"

    | Annot (typ, e) ->
      printf "[⟨@[";
      Types.print_type typ;
      printf "@]⟩@;<1 1>@[";
      print_exp e;
      printf "@]]"
end

module Constraints = struct
  type t = Eq of typ * typ
  type fail_obj = ..
  type fail_obj += ConstraintPos of t
  type failure =
    | Single : t -> failure
    | Nested : (fail_obj * failure) list -> failure
    | CaughtException : exn -> failure
  type 'where effect = Constrain of t list * (fail_obj * failure) option

  let print_constraint (Eq (s,t)) =
    Types.print_type s;
    printf " = ";
    Types.print_type t

  let empty = Constrain ([], None)
  let empty_state : t list * (fail_obj * failure) list = ([], [])
  let reducer state result =
    let (successes, failures) = state in
    let Constrain (new_successes, failure_opt) = result in
    match failure_opt with
    | None    -> (new_successes @ successes, failures)
    | Some wf -> (new_successes @ successes, wf :: failures)
  let guard test (successes, failures) =
    if List.length failures != 0
    then Constrain (successes, Some (test, Nested (failures)))
    else Constrain (successes, None)
  let combine_all list = List.fold_left reducer empty_state list

  let fail  w f =
    printf "!! constraint failure !!\n";
    Constrain ([],  Some (w, Single f))
  let success t = Constrain ([t], None)
  let caught_exception w e = Constrain ([], Some (w, CaughtException e))

  let rec constrain w t1 t2 =
    printf "comparing ";
    Types.print_type t1;
    printf " and ";
    Types.print_type t2;
    printf "\n";
    let eq = Eq (t1, t2) in
    let eqr = Eq (t2, t1) in
    try match t1, t2 with
    | TVar n, _ -> success eq
    | _, TVar m -> success eqr
    | TCon n, TCon m when n = m -> success eq
    | TCon n, TCon m -> fail w eq
    | TCon _, _ -> fail w eq
    | _, TCon _ -> fail w eqr
    | TApp (n, xs), TApp (m, ys) when n = m && List.(length xs = length ys) ->
         List.combine xs ys
      |> List.map (fun (x, y) -> constrain (ConstraintPos (Eq (x, y))) x y)
      |> combine_all
      |> guard w
    | TApp _, TApp _ -> fail w eq
    | Poly _, Poly _ -> raise (Lazy "do we need polytype constraints?")
    | _, _ -> fail w eq
    with e -> caught_exception w e
end

module TypeSystem = struct
  open List
  module Map = Exprs.Map
  type tenv = typ Map.t

  let map_tenv_types f tenv = Map.map_values_to_list f tenv

  let abstract tenv typ =
    let open Types.Set in
    let bound_vars = combine_all (map_tenv_types Types.free_vars tenv) in
    Poly (diff (Types.free_vars typ) bound_vars, typ)

  type Constraints.fail_obj += ExprPos of expression
  exception Name_not_found of varname
  let rec collect_constraints (tenv : tenv) (exp : expression):
      expression * typ * expression Constraints.effect =
    print_newline ();
    printf "@[<2>collect_constraints tenv=[@[<b 0>";
    print_list
      (fun () -> printf "@ ")
      (fun (n, typ) -> printf "%d: " n; Types.print_type typ)
      (Map.to_list tenv);
    printf "@]]@ expr = @[";
    Exprs.print_exp exp;
    printf "@]@]\n";
    let open Constraints in
    let annot exp typ eff = Annot (typ, exp), typ, eff in
    match exp with
    | Literal l ->
      annot exp (literal_type tenv l) empty
    | Var n ->
      (match Map.find_opt n tenv with
      | None -> raise (Name_not_found n)
      | Some found -> annot exp (Types.instantiate found) empty)
    | Call (f, args) ->
      let tvar = gentvar () in
      let annot_f, f_type, ffx = collect_constraints tenv f in
      let annot_args, arg_types, afx =
        List.map (collect_constraints tenv) args |> split3
      in
      let finalfx =
        constrain (ExprPos exp) f_type (TApp (Ids.tfun, arg_types @ [tvar]))
           :: ffx :: afx
        |> combine_all
        |> guard (ExprPos exp)
      in annot (Call (annot_f, annot_args)) tvar finalfx
    | If (c, y, n) ->
      let annot_c, c_type, cfx = collect_constraints tenv c in
      let annot_y, y_type, yfx = collect_constraints tenv y in
      let annot_n, n_type, nfx = collect_constraints tenv n in
      let finalfx = 
        combine_all [constrain (ExprPos exp) y_type n_type; cfx; yfx; nfx]
        |> guard (ExprPos exp)
      in
      annot (If (annot_c, annot_y, annot_n)) y_type finalfx
    | Let (name, init_value, body) ->
      let tvar = gentvar () in
      let tenv_inner = Map.add name tvar tenv in
      let annot_v, v_type, vfx = let_abstract tenv_inner init_value in
      let annot_b, b_type, bfx = collect_constraints tenv_inner body in
      guard (ExprPos exp) (combine_all [vfx; bfx; constrain (ExprPos exp) tvar v_type])
      |> annot (Let (name, annot_v, annot_b)) b_type
    | Func (params, body) ->
      let new_binds, domains = zipmap (fun _ -> gentvar ()) params in
      let tenv_body = Map.add_all tenv new_binds in
      let annot_body, body_type, bodyfx = collect_constraints tenv_body body in
      annot
        (Func (params, annot_body))
        (TApp (Ids.tfun, domains @ [body_type]))
        bodyfx 
    | Annot (desired, body) ->
      let annot_body, body_type, bodyfx = collect_constraints tenv body in
      let finalfx =
         combine_all [constrain (ExprPos exp) desired body_type; bodyfx]
      |> guard (ExprPos exp)
      in
      Annot (desired, annot_body), desired, finalfx
  and let_abstract tenv exp =
    match collect_constraints tenv exp with
    | Annot (_, inner), typ, fx ->
      let abstracted = abstract tenv typ in
      Annot (abstracted, inner), abstracted, fx
    | _ -> raise (Invariant "All types from collect_constraints must be annotated")
  and literal_type _tenv obj =
    match obj with
    | OUnit     -> TCon (Ids.tunit)
    | OInt _    -> TCon (Ids.tint)
    | OString _ -> TCon (Ids.tstring)
    | OBool _   -> TCon (Ids.tbool)
    | OFunc _   -> raise Todo
end

let poly generics mono = Poly (Types.Set.of_list generics, mono)
let func domains ret = TApp (Ids.tfun, domains @ [ret])
let tvar id = TVar id
let tint = TCon Ids.tint
let tbool = TCon Ids.tbool
let tlist typ = TApp (20, [typ])
let tcons = tlist (tvar 20001) |> func [tvar 20001; tlist (tvar 20001)]  |> poly [20001]
let tcar  = func [tlist (tvar 20003)] (tvar 20003) |> poly [20003]
let tcdr  = func [tlist (tvar 20004)] (tvar 20004) |> poly [20004]
let tsucc = func [tint] tint
let tnull = func [tlist (tvar 20005)] tbool |> poly [20005]
let tnil  = tlist (tvar 20006) |> poly [20006]
let ncons = 30001
let ncar  = 30002
let ncdr  = 30003
let nsucc = 30004
let nnull = 30005
let nnil  = 30006
let econs = Var ncons
let ecar  = Var ncar
let ecdr  = Var ncdr
let esucc = Var nsucc
let enull = Var nnull
let enil  = Var nnil
let tenv  =
     [(ncons, tcons); (ncar, tcar); (ncdr, tcdr); (nsucc, tsucc);
      (nnull, tnull); (nnil, tnil)]
  |> Exprs.Map.of_list

let nf    = 30101
let nlist = 30102
let nmap  = 30103
let ef    = Var nf
let elist = Var nlist
let emap  = Var nmap
let bmap  =
  Func ([nf; nlist],
    If (
      Call (
        enull,
        [elist]
      ),
      Call (
        econs,
        [
          Call (
            ef,
            [
              Call (
                ecar,
                [elist]
              )
            ]
          );
          Call (
            emap,
            [
              ef;
              Call (
                ecdr,
                [elist]
              )
            ]
          )
        ]
      ),
      enil
    )
  )
let bprogram =
  Let (nmap, bmap,
   Call (emap, [esucc;
    Call (econs, [Literal (OInt 1);
     Call (econs, [Literal (OInt 2);
      Call (econs, [Literal (OInt 3);
       enil])])])]))
let btyped, btype, (Constraints.Constrain (bconstraints, bfailure))
  = TypeSystem.collect_constraints tenv bprogram

;; 
printf "Constraints: \n";
print_list (fun () -> printf "\n") Constraints.print_constraint bconstraints;
print_newline ();
;;
set_margin 80
;;
print_flush ();
printf "Input program:@;<1 2>@[";
Exprs.print_exp bprogram;
printf "@]";
print_newline ();
;;
print_flush ();
printf "Resulting program:@;<1 2>@[";
Exprs.print_exp btyped;
printf "@]";
print_newline ();
(*

1000 = (int -> int) -> int -> int
1001 = int -> int
1002 = int list
1003 = bool
1004 = int
1005 = int list
1006 = int
1007 = int
1008 = int
1009 = int
1010 = int list
1011 = int
1012 = int
1013 = int
1014 = int list
1015 = int list
1016 = int
1017 = int list
1018 = int
1019 = int list
1020 = int
1021 = int

*)


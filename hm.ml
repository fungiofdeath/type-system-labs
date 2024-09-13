exception Todo                (* not finished *)
exception Lazy of string      (* too lazy to handle *)
exception Invariant of string (* some invariant violated *)
let todo _ = raise Todo

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

module Show = struct
  type t = Show of (unit -> unit)
  let show (Show f) = f ()
end

type typname = int
module TypnameHelper = Helper.Make(
  struct
    type comparable = typname
    let compare x y = x - y
  end
)

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

end

module Context = struct
  type t = Ctx of {
    var_names  : string Exprs.Map.t;
    typ_names : string Types.Map.t;
    env : typ Exprs.Map.t;
  }

  let env (Ctx { env }) = env
  let update (Ctx { var_names; typ_names }) new_env =
    Ctx { env = new_env; var_names; typ_names }
  let add name typ ctx = env ctx |> Exprs.Map.add name typ |> update ctx
  let add_all binds ctx = Exprs.Map.add_all (env ctx) binds |> update ctx
  let find_opt name ctx = env ctx |> Exprs.Map.find_opt name
  let find_or  name default ctx = env ctx |> Exprs.Map.find_or name default

  module Constants = struct
    let error   = 0
    let ga      = 1
    let gb      = 2

    let tunit   = 100
    let tbool   = 101
    let tstring = 102
    let tint    = 103
    let tfun    = 104
    let tlist   = 105

    let nsucc   = 200
    let nplus   = 201
    let nminus  = 202
    let ntimes  = 203
    let ndiv    = 204
    let nequal  = 205

    let nnull   = 300
    let ncons   = 301
    let ncar    = 302
    let ncdr    = 303
    let nnil    = 305

    let nslen   = 400
    let nsplus  = 401
    let nsnth   = 402

    let tsucc   = TApp (tfun, [TVar tint; TVar tint])
    let tplus   = TApp (tfun, [TVar tint; TVar tint])
    let tminus  = TApp (tfun, [TVar tint; TVar tint])
    let ttimes  = TApp (tfun, [TVar tint; TVar tint])
    let tdiv    = TApp (tfun, [TVar tint; TVar tint])
    let tequal  = TApp (tfun, [TVar tint; TVar tbool])

    let tnull   = Poly (Types.Set.of_list [ga], TApp (tfun, [TApp (tlist, [TVar ga]); TVar tbool]))
    let tnil    = Poly (Types.Set.of_list [ga], TApp (tlist, [TVar ga]))
    let tcons   = Poly (Types.Set.of_list [ga], TApp (tfun, [TVar ga; TApp (tlist, [TVar ga]); TApp (tlist, [TVar ga])]))
    let tcar    = Poly (Types.Set.of_list [ga], TApp (tfun, [TApp (tlist, [TVar ga]); TVar ga]))
    let tcdr    = Poly (Types.Set.of_list [ga], TApp (tfun, [TApp (tlist, [TVar ga]); TVar ga]))

    let tslen   = TApp (tfun, [TVar tstring; TVar tbool])
    let tsplus  = TApp (tfun, [TVar tstring; TVar tstring; TVar tstring])
    let tsnth   = TApp (tfun, [TVar tstring; TVar tint; TVar tint])
  end

  let create () =
    let open Constants in
    Ctx {
      var_names = Exprs.Map.of_list [
        (nsucc,   "succ");
        (nplus,   "plus");
        (nminus,  "minus");
        (ntimes,  "times");
        (ndiv,    "div");
        (nequal,  "equal");
        (nnull,   "null");
        (ncons,   "cons");
        (ncar,    "car");
        (ncdr,    "cdr");
        (nnil,    "nil");
        (nslen,   "slen");
        (nsplus,  "splus");
        (nsnth,   "snth");
      ];
      typ_names = Types.Map.of_list [
        (tunit,   "unit");
        (tint,    "int");
        (tbool,   "bool");
        (tstring, "string");
        (tfun,    "fn");
        (tlist,   "list");
      ];
      env = Exprs.Map.of_list [
        (nsucc,   tsucc);
        (nplus,   tplus);
        (nminus,  tminus);
        (ntimes,  ttimes);
        (ndiv,    tdiv);
        (nequal,  tequal);
        (nnull,   tnull);
        (ncons,   tcons);
        (ncar,    tcar);
        (ncdr,    tcdr);
        (nnil,    tnil);
        (nslen,   tslen);
        (nsplus,  tsplus);
        (nsnth,   tsnth);
      ];
    }
end

module Ids = Context.Constants

module PPrint = struct
  open Format

  let rec print_list sep f list =
    match list with
    | [] -> ()
    | x::[] -> f x
    | x::xs -> f x; sep (); print_list sep f xs

  type name_env = Names of {
    mutable already_unknown_vars  : Exprs.Set.t;
    mutable already_unknown_types : Types.Set.t;
    mutable known_vars    : string Exprs.Map.t;
    mutable known_types   : string Types.Map.t;
    mutable tapp_printers : ((typ -> unit) -> typ list -> unit) Types.Map.t
  }

  let of_ctx ctx = 
    let Context.Ctx { var_names; typ_names; } = ctx in
    Names {
      already_unknown_vars  = Exprs.Set.empty;
      already_unknown_types = Types.Set.empty;
      known_vars  = var_names;
      known_types = typ_names;
      tapp_printers = Types.Map.of_list [
        (Ids.tfun, fun print_type typs ->
                    let butlast, last = splitlast typs in
                    printf "fn(";
                    print_list (fun () -> printf ", ") print_type butlast;
                    printf ") -> ";
                    print_type last);
      ];
    }
  
  let create () = of_ctx (Context.create ())

  let print_var_name (Names nenv) name =
    if Exprs.Set.mem name (nenv.already_unknown_vars)
    then printf "x_%d" name
    else
      match Exprs.Map.find_opt name nenv.known_vars with
      | Some name -> printf "%s" name
      | None -> (
          nenv.already_unknown_vars <-
            Exprs.Set.add name nenv.already_unknown_vars;
          printf "x_%d" name
      )

  let print_obj lit =
    match lit with
    | OUnit -> printf "()"
    | OInt n -> printf "%d" n
    | OBool b -> printf "%b" b
    | OString s -> printf "%s" s
    | OFunc _ -> printf "<closure>"

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
    | TCon n -> printf "t%s" (type_name n)
    | TVar n -> printf "T%s" (type_name n)
    | TApp (n, xs) ->
      (* if n == Ids.tfun
      then
        let butlast, last = splitlast xs in
        printf "fn(";
        print_list (fun () -> printf ", ") print_type butlast;
        printf ") -> ";
        print_type last
      else ( *)
        printf "t%s(" (type_name n);
        print_list (fun () -> printf ", ") print_type xs;
        printf ")"
      (* ) *)
    | Poly (binds, mono) ->
      printf "for {";
      print_list (fun () -> printf ", ") print_int (Types.Set.to_list binds);
      printf "}. ";
      print_type mono

  let rec print_exp nenv exp =
    let print_careful exp =
      match exp with
      | Literal _ | Var _ -> print_exp nenv exp
      | _ -> printf "(@["; print_exp nenv exp; printf "@])"
    in
    match exp with
    | Literal l -> print_obj l
    | Var n -> print_var_name nenv n
    | Call (f, args) ->
      printf "@[<hv>@[";
      print_careful f;
      printf "@]@ @[";
      print_list (fun () -> printf "@]@ @[") print_careful args;
      printf "@]@]"

    | If (c, y, n) ->
      printf "@[<hv>@[if@;<1 2>@[";
      print_exp nenv c;
      printf "@]@]@ @[then@;<1 2>@[";
      print_exp nenv y;
      printf "@]@]@ @[else@;<1 2>@[";
      print_exp nenv n;
      printf "@]@]@]"

    | Let (name, init_value, body) ->
      printf "let@ ";
      print_var_name nenv name;
      printf "@ :=@;<1 2>@[";
      print_exp nenv init_value;
      printf "@]@;in@;<1 2>@[";
      print_exp nenv body;
      printf "@]"

    | Func (params, body) ->
      printf "@[<hv>@[\\@[";
      print_list (fun () -> printf "@ ") (print_var_name nenv) params;
      printf "@]@]@;<1 0>=>@]@;<1 2>@[<hov>";
      print_exp nenv body;
      printf "@]"

    | Annot (typ, e) ->
      printf "[⟨@[";
      print_type typ;
      printf "@]⟩@;<1 1>@[";
      print_exp nenv e;
      printf "@]]"
end

module Constraints = struct
  type t = Eq of typ * typ
  type failure =
    | Single : string * t -> failure
    | Nested : (Show.t * failure) list -> failure
    | CaughtException : exn -> failure
  type 'where effect = Constrain of t list * (Show.t * failure) option

  let print_constraint (Eq (s,t)) =
    PPrint.print_type s;
    Format.printf " = ";
    PPrint.print_type t;
    Format.printf ","

  let rec print_failure failure =
    match failure with
    | Single (reason, constraint_) ->
      Format.printf "@[<v>";
      print_constraint constraint_;
      Format.printf ":@;%s@]@;" reason
    | Nested failures ->
      failures |>
      List.iter
        (fun (showable, failure) ->
          Format.printf "@[<v>at @[";
          Show.show showable;
          Format.printf "@]@;|";
          print_failure failure;
          Format.printf "@]")
    | CaughtException _ -> Format.printf "caught exception"

  let empty = Constrain ([], None)
  let empty_state : t list * (Show.t * failure) list = ([], [])
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

  let fail where why f =
    print_endline "!! constraint failure !!";
    Constrain ([],  Some (where, Single (why, f)))
  let success t = Constrain ([t], None)
  let caught_exception w e = Constrain ([], Some (w, CaughtException e))

  let rec constrain w t1 t2 =
    Format.printf "comparing ";
    PPrint.print_type t1;
    Format.printf " and ";
    PPrint.print_type t2;
    Format.print_newline ();
    let eq = Eq (t1, t2) in
    let eqr = Eq (t2, t1) in
    let hide c = Show.Show (fun () -> print_constraint c) in
    try match t1, t2 with
    | Poly (_, ma), Poly (_, mb) ->
      [constrain (hide eq) ma mb] |> combine_all |> guard w
    | Poly (set, mono), x when Types.Set.is_empty set ->
      [constrain (hide eq) mono x] |> combine_all |> guard w
    | Poly _, _ -> fail w "polytypes and monotypes do not match" eq
    | _, Poly (set, mono) -> constrain w t2 t1
    | TVar n, _ -> success eq
    | _, TVar m -> success eqr
    | TCon n, TCon m when n = m -> success eq
    | TCon n, TCon m -> fail w "Types do not match" eq
    | TCon _, _ -> fail w "ctypes cannot be xtypes" eq
    | _, TCon _ -> fail w "ctypes cannot be xtypes" eqr
    | TApp (n, xs), TApp (m, ys) when n = m && List.(length xs = length ys) ->
         List.combine xs ys
      |> List.map (fun (x, y) -> constrain (hide eq) x y)
      |> combine_all
      |> guard w
    | TApp _, TApp _ -> fail w "Mismatched heads or args" eq
    with e -> caught_exception w e
end

module Solver = struct
  open List
  module Map = Exprs.Map
  type tenv = Context.t

  let map_tenv_types f tenv = Map.map_values_to_list f tenv

  let abstract tenv typ =
    let tenv_frees = Context.env tenv |> Map.map_values_to_list Types.free_vars in
    let bound_vars = Types.Set.combine_all tenv_frees in
    Poly (Types.Set.diff (Types.free_vars typ) bound_vars, typ)

  exception Name_not_found of varname

  let rec collect_constraints (tenv : tenv) (exp : expression):
      expression * typ * expression Constraints.effect =
    Format.print_newline ();
    Format.printf "@[<2>collect_constraints tenv=[@[<b 0>";
    PPrint.print_list
      (fun () -> Format.printf "@ ")
      (fun (n, typ) ->
        Format.printf "%d: " n;
        PPrint.print_type typ)
      (Map.to_list (Context.env tenv));
    Format.printf "@]]@ expr = @[";
    PPrint.print_exp (PPrint.create ()) exp;
    Format.printf "@]@]\n";
    let open Constraints in
    let annot exp typ eff = Annot (typ, exp), typ, eff in
    let pos_of tenv exp =
      Show.Show (fun () -> PPrint.(print_exp (of_ctx tenv) exp))
    in
    let pos = pos_of tenv exp in
    match exp with
    | Literal l ->
      annot exp (literal_type tenv l) empty
    | Var n ->
      (match Context.find_opt n tenv with
      | None -> raise (Name_not_found n)
      | Some found -> annot exp (Types.instantiate found) empty)
    | Call (f, args) ->
      let tvar = gentvar () in
      let annot_f, f_type, ffx = collect_constraints tenv f in
      let annot_args, arg_types, afx =
        List.map (collect_constraints tenv) args |> split3
      in
      let finalfx =
        constrain pos f_type (TApp (Ids.tfun, arg_types @ [tvar]))
           :: ffx :: afx
        |> combine_all
        |> guard pos
      in annot (Call (annot_f, annot_args)) tvar finalfx
    | If (c, y, n) ->
      let annot_c, c_type, cfx = collect_constraints tenv c in
      let annot_y, y_type, yfx = collect_constraints tenv y in
      let annot_n, n_type, nfx = collect_constraints tenv n in
      let finalfx = 
        combine_all [constrain pos y_type n_type; cfx; yfx; nfx]
        |> guard pos
      in
      annot (If (annot_c, annot_y, annot_n)) y_type finalfx
    | Let (name, init_value, body) ->
      let tvar = gentvar () in
      let tenv_value = Context.add name tvar tenv in
      let annot_v, v_type, vfx = collect_constraints tenv_value init_value in
      let tenv_body = Context.add name (abstract tenv_value v_type) tenv in
      let annot_b, b_type, bfx = collect_constraints tenv_body body in
      combine_all [vfx; bfx; constrain pos tvar v_type]
      |> guard pos
      |> annot (Let (name, annot_v, annot_b)) b_type
    | Func (params, body) ->
      let new_binds, domains = zipmap (fun _ -> gentvar ()) params in
      let tenv_body = Context.add_all new_binds tenv in
      let annot_body, body_type, bodyfx = collect_constraints tenv_body body in
      annot
        (Func (params, annot_body))
        (TApp (Ids.tfun, domains @ [body_type]))
        bodyfx 
    | Annot (desired, body) ->
      let annot_body, body_type, bodyfx = collect_constraints tenv body in
      let finalfx =
         combine_all [constrain pos desired body_type; bodyfx]
      |> guard pos
      in
      Annot (desired, annot_body), desired, finalfx
  and literal_type _tenv obj =
    match obj with
    | OUnit     -> TCon (Ids.tunit)
    | OInt _    -> TCon (Ids.tint)
    | OString _ -> TCon (Ids.tstring)
    | OBool _   -> TCon (Ids.tbool)
    | OFunc _   -> raise Todo
end

;;
print_endline "================     Loading program      ==================";
;;

let nfoo = 30000
let nf   = 30001
let nx   = 30002
let np   = 30003
let efoo = Var nfoo
let ef   = Var nf
let ex   = Var nx
let ep   = Var np
let bfunc =
  Func ([np],
    Call (
      Func ([nf], Call (ef, [Literal OUnit])),
      [
        Func ([np], Literal (OInt 1));
      ]
    )
  )
let bprogram =
  Let (nfoo, bfunc,
    Let (nx, Call (efoo, [Literal OUnit]),
      ex))

(* let tvar id = TVar id
let econs = Var Ids.ncons
let ecar  = Var Ids.ncar
let ecdr  = Var Ids.ncdr
let esucc = Var Ids.nsucc
let enull = Var Ids.nnull
let enil  = Var Ids.nnil

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
       enil])])])])) *)
;;
print_endline "Finished.";
print_endline "================ Solving type constraints ==================";
Format.set_margin 80
;;

let btyped, btype, (Constraints.Constrain (bconstraints, bfailure))
  = Solver.collect_constraints (Context.create ()) bprogram
;; 
print_endline "Finished.";
(match bfailure with
| None -> ()
| Some (showable, failure) ->
  Format.printf "Failed at @[";
  Show.show showable;
  Format.printf "@]:";
  Format.print_newline ();
  Constraints.print_failure failure;
  Format.print_newline ();
);
print_endline "================    Found Constraints     ==================";
PPrint.print_list
  (fun _ -> Format.print_newline ())
  Constraints.print_constraint bconstraints;
Format.print_newline ();
;;
;;
Format.printf "Input program:@;<1 2>@[";
PPrint.print_exp (PPrint.create ()) bprogram;
Format.printf "@]";
Format.print_newline ();
;;
Format.printf "Resulting program:@;<1 2>@[";
PPrint.print_exp (PPrint.create ()) btyped;
Format.printf "@]";
Format.print_newline ();

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


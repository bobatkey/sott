type 'a binder = B of string * 'a

type term =
  | Neutral of head * elims

  | Lam of term binder
  | Set
  | Pi of term * term binder
  | Sigma of term * term binder
  | Pair of term * term
  | Bool
  | True
  | False

  | TyEq of term * term
  | TmEq of { tm1 : term; ty1 : term; tm2 : term; ty2 : term }

  (* proof constructors *)
  | Subst of { ty_s : term
             ; ty_t : term binder
             ; tm_x : term
             ; tm_y : term
             ; tm_e : term
             }
  | Refl
  | Coh
  | Funext of term binder binder binder

  (* placeholder for an erased proof term; only generated during
     reification. *)
  | Irrel

(*
    G, x : A, x' : A', e : [x : A == x' : A'] |- M : [f x : B x == g x' : B' x']
  -------------------------------------------------------------------------------
            G |- funext M : [f : (x : A) -> B == g : (x : A') -> B']


        -----------------------------------------------
           G |- coh : [a : A = coerce(a,A,B,p) : B]
*)

and head =
  | Bound  of int
  | Free   of string
  | Coerce of { coercee  : term
              ; src_type : term
              ; tgt_type : term
              ; eq_proof : term
              }

and elims =
  | Nil
  | App     of elims * term
  | If      of elims * term binder * term * term
  | Project of elims * [`fst | `snd]

module AlphaEquality = struct

  let binder2 k (B (_,t1)) (B (_,t2)) =
    k t1 t2

  let rec equal_term t1 t2 = match t1, t2 with
    | Neutral (h1, es1), Neutral (h2, es2) ->
       equal_head h1 h2 && equal_elims es1 es2
    | Lam t1, Lam t2 ->
       binder2 equal_term t1 t2
    | Set, Set ->
       true
    | Pi (s1, t1), Pi (s2, t2)
    | Sigma (s1, t1), Sigma (s2, t2) ->
       equal_term s1 s2 && binder2 equal_term t1 t2
    | Pair (s1, t1), Pair (s2, t2) ->
       equal_term s1 s2 && equal_term t1 t2
    | Bool, Bool
    | True, True
    | False, False ->
       true
    | TyEq (s1, t1), TyEq (s2, t2) ->
       equal_term s1 s2 && equal_term t1 t2
    | TmEq { tm1;      ty1;      tm2;      ty2 },
      TmEq { tm1=tm1'; ty1=ty1'; tm2=tm2'; ty2=ty2' } ->
       equal_term tm1 tm1' &&
       equal_term ty1 ty1' &&
       equal_term tm2 tm2' &&
       equal_term ty2 ty2'
    | Subst { ty_s;       ty_t;       tm_x;       tm_y;       tm_e },
      Subst { ty_s=ty_s'; ty_t=ty_t'; tm_x=tm_x'; tm_y=tm_y'; tm_e=tm_e' } ->
       equal_term ty_s ty_s' &&
       binder2 equal_term ty_t ty_t' &&
       equal_term tm_x tm_x' &&
       equal_term tm_y tm_y' &&
       equal_term tm_e tm_e'
    | Refl, Refl
    | Coh,  Coh ->
       true
    | Funext e, Funext e' ->
       binder2 (binder2 (binder2 equal_term)) e e'
    | Irrel, Irrel ->
       true
    | _, _ ->
       false

  and equal_head h1 h2 = match h1, h2 with
    | Bound i, Bound j -> i = j
    | Free nm, Free nm' -> nm = nm'
    | Coerce { coercee; src_type; tgt_type; eq_proof },
      Coerce { coercee=coercee'; src_type=src_type'
             ; tgt_type=tgt_type'; eq_proof=eq_proof' } ->
       equal_term coercee coercee' &&
       equal_term src_type src_type' &&
       equal_term tgt_type tgt_type' &&
       equal_term eq_proof eq_proof'
    | _, _ ->
       false

  and equal_elims e1 e2 = match e1, e2 with
    | Nil, Nil ->
       true
    | App (es, t), App (es', t') ->
       equal_elims es es' && equal_term t t'
    | If (es, ty, tm_t, tm_f),
      If (es', ty', tm_t', tm_f') ->
       equal_elims es es' &&
       binder2 equal_term ty ty' &&
       equal_term tm_t tm_t' &&
       equal_term tm_f tm_f'
    | Project (es, dir), Project (es', dir') ->
       dir = dir' && equal_elims es es'
    | _, _ ->
       false

end

(**********************************************************************)
module Scoping : sig
  val bind : string -> term -> term binder

  val bind3 : string -> string -> string -> term -> term binder binder binder

  val bind_anon : term -> term binder

  val close : string -> term binder -> term

  val close3 : string -> string -> string -> term binder binder binder -> term
end = struct
  let binder k j = function
    | B (nm, t) -> B (nm, k (j+1) t)

  let traverse ~free ~bound j tm =
    let rec traverse_term j = function
      | Neutral (head, elims) ->
         Neutral (traverse_head j head, traverse_elims j elims)
      | Lam t ->
         Lam (binder traverse_term j t)
      | Set ->
         Set
      | Pi (s, t) ->
         Pi (traverse_term j s, binder traverse_term j t)
      | Sigma (s, t) ->
         Sigma (traverse_term j s, binder traverse_term j t)
      | Pair (t1, t2) ->
         Pair (traverse_term j t1, traverse_term j t2)
      | TyEq (s, t) ->
         TyEq (traverse_term j s, traverse_term j t)
      | TmEq {tm1;ty1;tm2;ty2} ->
         TmEq { tm1 = traverse_term j tm1
              ; ty1 = traverse_term j ty1
              ; tm2 = traverse_term j tm2
              ; ty2 = traverse_term j ty2
              }
      | (Bool | True | False) as t -> t
      | Subst { ty_s; ty_t; tm_x; tm_y; tm_e } ->
         Subst { ty_s = traverse_term j ty_s
               ; ty_t = binder traverse_term j ty_t
               ; tm_x = traverse_term j tm_x
               ; tm_y = traverse_term j tm_y
               ; tm_e = traverse_term j tm_e
               }
      | (Refl | Coh) as t -> t
      | Funext tm ->
         Funext (binder (binder (binder traverse_term)) j tm)
      | Irrel ->
         failwith "internal error: attempt to bind in an erased proof term"

    and traverse_head j = function
      | Bound i -> bound i j
      | Free nm -> free nm j
      | Coerce { coercee; src_type; tgt_type; eq_proof } ->
         Coerce { coercee  = traverse_term j coercee
                ; src_type = traverse_term j src_type
                ; tgt_type = traverse_term j tgt_type
                ; eq_proof = traverse_term j eq_proof
                }

    and traverse_elims j = function
      | Nil ->
         Nil
      | App (elims, tm) ->
         App (traverse_elims j elims, traverse_term j tm)
      | If (elims, ty, tm_t, tm_f) ->
         If (traverse_elims j elims,
             binder traverse_term j ty,
             traverse_term j tm_t,
             traverse_term j tm_f)
      | Project (elims, component) ->
         Project (traverse_elims j elims, component)
    in
    traverse_term j tm

  let close_term x =
    traverse
      ~free:(fun nm j -> Free nm)
      ~bound:(fun i j -> if i = j then Free x else Bound i)

  let bind_term x =
    traverse
      ~free:(fun nm j -> if nm = x then Bound j else Free nm)
      ~bound:(fun i j -> Bound i)

  let bind x t =
    B (x, bind_term x 0 t)

  let bind3 x y z t =
    let t1 = B (z, bind_term z 0 t) in
    let t2 = B (y, binder (bind_term y) 0 t1) in
    let t3 = B (x, binder (binder (bind_term x)) 0 t2) in
    t3

  let bind_anon t =
    B ("x", t)

  let close nm (B (_nm, tm)) =
    (* FIXME: choose the fresh name here, using the binder provided
       one as a hint. *)
    close_term nm 0 tm

  let close3 nm1 nm2 nm3 (B (_, B (_, B (_, t)))) =
    close_term nm3 0 (close_term nm2 1 (close_term nm1 2 t))
end

(******************************************************************************)
(* Semantic interpretation *)

type shift = int

type value =
  | V_Neutral of v_head * v_elims
  | V_Lam     of value v_binder
  | V_Set
  | V_Bool
  | V_True
  | V_False
  | V_Pi      of value * value v_binder
  | V_Sigma   of value * value v_binder
  | V_Pair    of value * value
  | V_TyEq    of value * value
  | V_TmEq    of { s : value; s_ty : value; t : value; t_ty : value }
  | V_Irrel

and 'a v_binder =
  | VB of string * (value -> 'a)

and v_elims =
  | E_Nil
  | E_App of v_elims * value
  | E_If  of v_elims * value v_binder * value * value
  | E_Project of v_elims * [`fst|`snd]

and v_head =
  | H_Var  of { shift : shift; typ : value }
  | H_Free of { name  : string; typ : value }
  | H_Coe  of { coercee  : value
              ; src_type : value
              ; tgt_type : value
              }


let apply v1 v2 = match v1 with
  | V_Lam (VB (_, f)) -> f v2
  | V_Neutral (h, es) -> V_Neutral (h, E_App (es, v2))
  | _                 -> failwith "internal type error"

let vfst = function
  | V_Pair (v, _) ->
     v
  | V_Neutral (h, es) ->
     V_Neutral (h, E_Project (es, `fst))
  | _ ->
     failwith "internal error: type error in vfst"

let vsnd = function
  | V_Pair (_, v) ->
     v
  | V_Neutral (h, es) ->
     V_Neutral (h, E_Project (es, `snd))
  | _ ->
     failwith "internal error: type error in vsnd"

let rec eval_elims t = function
  | E_Nil -> t
  | E_App (es, v) -> apply (eval_elims t es) v
  | E_If (es, ty, v_t, v_f) ->
     (match eval_elims t es with
       | V_True        -> v_t
       | V_False       -> v_f
       | V_Neutral (h, es) ->
          V_Neutral (h, E_If (es, ty, v_t, v_f))
       | _ ->
          failwith "type error")
  | E_Project (es, component) ->
     (match eval_elims t es, component with
       | V_Pair (v, _), `fst -> v
       | V_Pair (_, v), `snd -> v
       | V_Neutral (h, es), _ ->
          V_Neutral (h, E_Project (es, component))
       | _  -> failwith "internal error: type error in projection")

let var ty i =
  V_Neutral (H_Var { shift = i; typ = ty }, E_Nil)

let free x ty =
  V_Neutral (H_Free { name = x; typ = ty }, E_Nil)

(**********************************************************************)
(* FIXME: equality test rather than reify to term and check for alpha
   equality? *)

let rec reify_type v i = match v with
  | V_Pi (s, VB (x, t)) ->
     Pi (reify_type s i, B (x, reify_type (t (var s i)) (i+1)))
  | V_Sigma (s, VB (x, t)) ->
     Sigma (reify_type s i, B (x, reify_type (t (var s i)) (i+1)))
  | V_Set ->
     Set
  | V_Bool ->
     Bool
  | V_TyEq (s, t) ->
     TyEq (reify_type s i, reify_type t i)
  | V_TmEq {s; s_ty; t; t_ty} ->
     TmEq { tm1 = reify s_ty s i
          ; ty1 = reify_type s_ty i
          ; tm2 = reify t_ty t i
          ; ty2 = reify_type t_ty i
          }
  | V_Neutral (h, es) ->
     reify_neutral h es i
  | _ ->
     failwith "internal error: refiy_type -- not in canonical form"

and reify ty v i = match ty, v with
  | V_Pi (s, VB (_, t)), V_Lam (VB (x, body)) ->
     let v = var s i in Lam (B (x, reify (t v) (body v) (i+1)))
  | V_Pi (s, VB (x, t)), f ->
     let v = var s i in Lam (B (x, reify (t v) (apply f v) (i+1)))
  | V_Sigma (s, VB (_, t)), p ->
     Pair (reify s (vfst p) i, reify (t (vfst p)) (vsnd p) i)
  | V_TyEq _, v       -> Irrel
  | V_TmEq _, v       -> Irrel
  | V_Bool,   V_True  -> True
  | V_Bool,   V_False -> False
  | V_Set,    v       -> reify_type v i
  | _,        V_Neutral (h, es) -> reify_neutral h es i
  | _                 -> failwith "internal error: reification failed"

and reify_neutral h es i = match h with
  | H_Var { shift; typ } ->
     let es, _ = reify_elims h typ es i in
     Neutral (Bound (i-shift-1), es)
  | H_Free { name; typ } ->
     let es, _ = reify_elims h typ es i in
     Neutral (Free name, es)
  | H_Coe { coercee; src_type; tgt_type } ->
     let ty1_tm = reify_type src_type i in
     let ty2_tm = reify_type tgt_type i in
     if AlphaEquality.equal_term ty1_tm ty2_tm then
       reify src_type (eval_elims coercee es) i
     else
       let es, _ = reify_elims h tgt_type es i in
       Neutral (Coerce { coercee  = reify src_type coercee i
                       ; src_type = ty1_tm
                       ; tgt_type = ty2_tm
                       ; eq_proof = Irrel
                       }, es)

and reify_elims h ty es i = match es with
  | E_Nil ->
     Nil, ty
  | E_App (es, v) ->
     (match reify_elims h ty es i with
       | es, V_Pi (s, VB (_, t)) ->
          App (es, reify s v i), t v
       | _ ->
          failwith "internal error: type error reifying application")
  | E_If (es, VB (x, elim_ty), v_t, v_f) ->
     (match reify_elims h ty es i with
       | es', V_Bool ->
          If (es',
              B (x, reify_type (elim_ty (var V_Bool i)) (i+1)),
              reify (elim_ty V_True) v_t i,
              reify (elim_ty V_False) v_f i),
          elim_ty (V_Neutral (h, es))
       | _ ->
          failwith "internal error: type error reifying bool case switch")
  | E_Project (es, component) ->
     (match reify_elims h ty es i, component with
       | (reified_es, V_Sigma (s, _)), `fst ->
          Project (reified_es, `fst), s
       | (reified_es, V_Sigma (s, VB (_, t))), `snd ->
          Project (reified_es, `snd), t (V_Neutral (h, es))
       | _ ->
          failwith "internal error: type error reifying a projection")

let equal_types ty1 ty2 =
  let ty1 = reify_type ty1 0 in
  let ty2 = reify_type ty2 0 in
  AlphaEquality.equal_term ty1 ty2

let equal_terms tm1 tm2 ty =
  let tm1 = reify ty tm1 0 in
  let tm2 = reify ty tm2 0 in
  AlphaEquality.equal_term tm1 tm2

(**********************************************************************)
(* Contexts *)

(* FIXME: contexts ought to distinguish between 'global' (i.e bindings
   outwith the current term), and 'local'. *)

module Context : sig
  type t

  val empty : t
  val extend : t -> value -> string * t
  val lookup : string -> t -> (value, [>`VarNotFound of string]) result
  val lookup_exn : string -> t -> value * value option
  val extend_with_defn : string -> ty:value -> tm:value -> t -> t
end = struct
  module VarMap = Map.Make(String)

  type entry =
    { entry_type : value
    ; entry_defn : value option
    }
  
  type t =
    { next_var : int
    ; entries  : entry VarMap.t
    }

  let empty =
    { next_var = 0; entries = VarMap.empty }

  (* FIXME: what if we extend with a name that is already free in the
     term? *)
  let extend ctxt value =
    let var = "_x"^string_of_int ctxt.next_var in
    let entry = { entry_type = value; entry_defn = None } in
    var,
    { next_var = ctxt.next_var + 1
    ; entries  = VarMap.add var entry ctxt.entries
    }

  let lookup nm ctxt =
    match VarMap.find nm ctxt.entries with
      | exception Not_found ->
         Error (`VarNotFound nm)
      | {entry_type} ->
         Ok entry_type

  let lookup_exn nm ctxt =
    let {entry_type; entry_defn} = VarMap.find nm ctxt.entries in
    (entry_type, entry_defn)

  let extend_with_defn nm ~ty ~tm ctxt =
    let entry = { entry_type = ty; entry_defn = Some tm } in
    { ctxt with entries = VarMap.add nm entry ctxt.entries }
end

(******************************************************************************)
(* Evaluation: injection into the semantic 'value' domain. *)
module Evaluation : sig
  val eval0 : Context.t -> term -> value
  val eval1 : Context.t -> term binder -> value -> value
end = struct
  let rec coerce v src tgt = match v, src, tgt with
    | v, V_Bool, V_Bool -> v
    | v, V_Set,  V_Set  -> v
    | f, V_Pi (ty_s, VB (_, ty_t)), V_Pi (ty_s', VB (x, ty_t')) ->
       let x = match f with V_Lam (VB (x, _)) -> x | _ -> x in
       V_Lam
         (VB (x, fun s' ->
              let s = coerce s' ty_s' ty_s in
              let t = apply f s in
              coerce t (ty_t' s') (ty_t s)))
    | p, V_Sigma (ty_s, VB (_, ty_t)), V_Sigma (ty_s', VB (_, ty_t')) ->
       let s' = coerce (vfst p) ty_s ty_s' in
       V_Pair (s', coerce (vsnd p) (ty_t (vfst p)) (ty_t' s'))
    | _, V_TyEq _, V_TyEq _
    | _, V_TmEq _, V_TmEq _
    | _, V_Neutral _, _
    | _, _, V_Neutral _ ->
       V_Neutral (H_Coe { coercee = v; src_type = src; tgt_type = tgt }, E_Nil)
    | _ ->
       (* FIXME: ought to be a suspended falsity elimination *)
       V_Neutral (H_Coe { coercee = v; src_type = src; tgt_type = tgt }, E_Nil)

  let binder k (B (nm, tm)) env =
    VB (nm, fun v -> k tm (v::env))

  let evaluate ctxt tm =
    let rec eval tm env = match tm with
      | Neutral (h, es) -> eval_elims (eval_head h env) es env
      | Lam t           -> V_Lam (binder eval t env)
      | Set             -> V_Set
      | Pi (t1, t2)     -> V_Pi (eval t1 env, binder eval t2 env)
      | Sigma (s, t)    -> V_Sigma (eval s env, binder eval t env)
      | Pair (s, t)     -> V_Pair (eval s env, eval t env)
      | TyEq (s, t)     -> V_TyEq (eval s env, eval t env)
      | TmEq {tm1;ty1;tm2;ty2} ->
         V_TmEq { s    = eval tm1 env
                ; s_ty = eval ty1 env
                ; t    = eval tm2 env
                ; t_ty = eval ty2 env
                }
      | Bool  -> V_Bool
      | True  -> V_True
      | False -> V_False

      | Subst _ | Coh | Funext _ | Refl | Irrel ->
         V_Irrel

    and eval_head h env = match h with
      | Bound i -> List.nth env i (* FIXME: something better than lists? *)
      | Free nm ->
         (match Context.lookup_exn nm ctxt with
           | typ, None ->
              V_Neutral (H_Free { name = nm; typ }, E_Nil)
           | typ, Some defn ->
              defn)
      | Coerce { coercee; src_type; tgt_type } ->
         coerce (eval coercee env) (eval src_type env) (eval tgt_type env)

    and eval_elims scrutinee elims env = match elims with
      | Nil ->
         scrutinee
      | App (elims, tm) ->
         apply (eval_elims scrutinee elims env) (eval tm env)
      | If (elims, ty, tm_t, tm_f) ->
         (match eval_elims scrutinee elims env with
           | V_True  -> eval tm_t env
           | V_False -> eval tm_f env
           | V_Neutral (h, es) ->
              V_Neutral (h, E_If (es, binder eval ty env,
                                  eval tm_t env, eval tm_f env))
           | _ -> failwith "internal type error: eval_elims If")
      | Project (elims, `fst) ->
         vfst (eval_elims scrutinee elims env)
      | Project (elims, `snd) ->
         vsnd (eval_elims scrutinee elims env)
    in
    eval tm

  let eval0 ctxt tm = evaluate ctxt tm []
  let eval1 ctxt (B (_, tm)) v = evaluate ctxt tm [v]
end
  
(******************************************************************************)
type error_message =
  [ `Msg of string
  | `Type_mismatch of term * term
  | `VarNotFound of string
  ]

let rec is_type ctxt = function
  | Set ->
     Ok ()
  | Bool ->
     Ok ()
  | Pi (s, t) ->
     (match is_type ctxt s with
       | Ok () ->
          let x, ctxt = Context.extend ctxt (Evaluation.eval0 ctxt s) in
          is_type ctxt (Scoping.close x t)
       | Error msg ->
          Error msg)
  | Sigma (s, t) ->
     (match is_type ctxt s with
       | Ok () ->
          let x, ctxt = Context.extend ctxt (Evaluation.eval0 ctxt s) in
          is_type ctxt (Scoping.close x t)
       | Error msg ->
          Error msg)
  | TyEq (s, t) ->
     (match is_type ctxt s with
       | Ok ()     -> is_type ctxt t
       | Error msg -> Error msg)
  | TmEq {tm1; ty1; tm2; ty2} ->
     (match is_type ctxt ty1, is_type ctxt ty2 with
       | Ok (), Ok () ->
          let ty1 = Evaluation.eval0 ctxt ty1 in
          let ty2 = Evaluation.eval0 ctxt ty2 in
          (match has_type ctxt ty1 tm1, has_type ctxt ty2 tm2 with
            | Ok (), Ok () ->
               Ok ()
            | Error msg, _ ->
               Error msg
            | _, Error msg ->
               Error msg)
       | Error msg, _ ->
          Error msg
       | Ok _, Error msg ->
          Error msg)
  (* FIXME: only remaining possibility is Neutral: synthesise the type
     and check that it is Set for some set level. This would allow a
     hierarchy of Sets. *)
  | tm ->
     has_type ctxt V_Set tm

and has_type ctxt ty tm = match ty, tm with
  | V_Pi (s, VB (_, t)), Lam tm ->
     let x, ctxt = Context.extend ctxt s in
     has_type ctxt (t (free x s)) (Scoping.close x tm)
  | V_Sigma (s, VB (_, t)), Pair (tm_s, tm_t) ->
     (match has_type ctxt s tm_s with
       | Ok () ->
          let tm_s = Evaluation.eval0 ctxt tm_s in
          has_type ctxt (t tm_s) tm_t
       | Error msg ->
          Error msg)
  | V_Set, Bool ->
     Ok ()
  | V_Set, Pi (s, t) ->
     (match has_type ctxt V_Set s with
       | Ok () ->
          let x, ctxt = Context.extend ctxt (Evaluation.eval0 ctxt s) in
          has_type ctxt V_Set (Scoping.close x t)
       | Error msg ->
          Error msg)
  | V_Set, Sigma (s, t) ->
     (match has_type ctxt V_Set s with
       | Ok () ->
          let x, ctxt = Context.extend ctxt (Evaluation.eval0 ctxt s) in
          has_type ctxt V_Set (Scoping.close x t)
       | Error msg ->
          Error msg)
  | V_Set, TyEq (s, t) ->
     (match is_type ctxt s with
       | Ok ()     -> is_type ctxt t
       | Error msg -> Error msg)
  | V_Set, TmEq {tm1; ty1; tm2; ty2} ->
     (match is_type ctxt ty1, is_type ctxt ty2 with
       | Ok (), Ok () ->
          let ty1 = Evaluation.eval0 ctxt ty1 in
          let ty2 = Evaluation.eval0 ctxt ty2 in
          (match has_type ctxt ty1 tm1, has_type ctxt ty2 tm2 with
            | Ok (), Ok () ->
               Ok ()
            | _ ->
               Error (`Msg "term(s) not of right type in term equality"))
       | Error msg, _ ->
          Error msg
       | Ok _, Error msg ->
          Error msg)

  | V_Bool, (True | False) ->
     Ok ()

  | V_TyEq (ty1, ty2), Subst { ty_s; ty_t; tm_x; tm_y; tm_e } ->
     (match is_type ctxt ty_s with
       | Ok () ->
          (let ty_s = Evaluation.eval0 ctxt ty_s in
           match
             let x, ctxt = Context.extend ctxt ty_s in
             is_type ctxt (Scoping.close x ty_t)
           with
             | Ok () ->
                (let ty_t = Evaluation.eval1 ctxt ty_t in
                 match has_type ctxt ty_s tm_x, has_type ctxt ty_s tm_y with
                   | Ok (), Ok () ->
                      (let tm_x = Evaluation.eval0 ctxt tm_x in
                       let tm_y = Evaluation.eval0 ctxt tm_y in
                       let ty   =
                         V_TmEq { s = tm_x; s_ty = ty_s; t = tm_y; t_ty = ty_s }
                       in
                       match has_type ctxt ty tm_e with
                         | Ok () ->
                            if (equal_types (ty_t tm_x) ty1
                                && equal_types (ty_t tm_y) ty2)
                            then
                              Ok ()
                            else
                              Error (`Msg "type mismtach in subst")
                         | Error msg ->
                            Error msg)
                   | _ ->
                      Error (`Msg "problem in checking left and right bits of subst"))
             | Error msg ->
                Error msg)
       | Error msg ->
          Error msg)

  | V_TyEq (ty1, ty2), Refl ->
     if equal_types ty1 ty2 then
       Ok ()
     else
       Error (`Msg "types not equal in refl")

  | V_TmEq { s; s_ty; t; t_ty }, Refl ->
     if equal_types s_ty t_ty then
       (if equal_terms s t s_ty then
          Ok ()
        else
          Error (`Msg "terms not equal in refl"))
     else
       Error (`Msg "types not equal in refl")

  | V_TmEq { s=tm_f1; s_ty=V_Pi (s1, VB (_, t1))
           ; t=tm_f2; t_ty=V_Pi (s2, VB (_, t2))},
    Funext proof ->
     let x1, ctxt = Context.extend ctxt s1 in
     let x1v      = free x1 s1 in
     let x2, ctxt = Context.extend ctxt s2 in
     let x2v      = free x2 s2 in
     let xe, ctxt =
       Context.extend ctxt (V_TmEq {s=x1v; s_ty=s2; t=x2v; t_ty=s2}) in
     let proof    = Scoping.close3 x1 x2 xe proof in
     let reqd_ty  =
       V_TmEq { s    = apply tm_f1 x1v
              ; s_ty = t1 x1v
              ; t    = apply tm_f2 x2v
              ; t_ty = t2 x2v
              }
     in
     has_type ctxt reqd_ty proof

  | V_TmEq {s; s_ty; t; t_ty}, Coh ->
     let t' =
       V_Neutral (H_Coe { coercee = s; src_type = s_ty; tgt_type = t_ty }, E_Nil)
     in
     if equal_terms t t' t_ty then
       Ok ()
     else
       Error (`Msg "invalid coh")

  | ty, Neutral (h, elims) ->
     (match synthesise_elims_type ctxt h elims with
       | Ok ty' ->
          let ty = reify_type ty 0 in
          let ty' = reify_type ty' 0 in
          if AlphaEquality.equal_term ty ty'
          then Ok ()
          else Error (`Type_mismatch (ty, ty'))
       | Error msg ->
          Error msg)

  | ty, tm ->
     Error (`Msg "type error: pushed in type does not match term")

and synthesise_head_type ctxt = function
  | Bound _ ->
     failwith "internal error: bound variable has got free"

  | Free nm ->
     Context.lookup nm ctxt

  | Coerce { coercee; src_type; tgt_type; eq_proof } ->
     match is_type ctxt src_type, is_type ctxt tgt_type with
       | Ok (), Ok () ->
          let ty1 = Evaluation.eval0 ctxt src_type in
          let ty2 = Evaluation.eval0 ctxt tgt_type in
          (match has_type ctxt ty1 coercee,
                 has_type ctxt (V_TyEq (ty1, ty2)) eq_proof with
            | Ok (), Ok () ->
               Ok ty2
            | Error msg, _ ->
               Error msg
            | _, Error msg ->
               Error msg)
       | Error msg, _ ->
          Error msg
       | Ok (), Error msg ->
          Error msg

and synthesise_elims_type ctxt h = function
  | Nil ->
     synthesise_head_type ctxt h

  | App (elims, tm) ->
     (match synthesise_elims_type ctxt h elims with
       | Ok (V_Pi (s, VB (_, t))) ->
          (match has_type ctxt s tm with
            | Ok ()   -> Ok (t (Evaluation.eval0 ctxt tm))
            | Error e -> Error e)
       | Ok _    ->
          Error (`Msg "attempt to apply non function")
       | Error e ->
          Error e)

  | If (elims, elim_ty, tm_t, tm_f) ->
     (match synthesise_elims_type ctxt h elims with
       | Ok V_Bool ->
          (match
             let x, ctxt = Context.extend ctxt V_Bool in
             is_type ctxt (Scoping.close x elim_ty)
           with
             | Ok () ->
                let ty = Evaluation.eval1 ctxt elim_ty in
                (match (has_type ctxt (ty V_True) tm_t,
                        has_type ctxt (ty V_False) tm_f) with
                  | Ok (), Ok () ->
                     Ok (ty (Evaluation.eval0 ctxt (Neutral (h, elims))))
                  | _ ->
                     Error (`Msg "error in branches of if"))
             | Error msg ->
                Error msg)
       | Ok _ ->
          Error (`Msg "attempt to eliminate non boolean")
       | Error msg ->
          Error msg)

  | Project (elims, `fst) ->
     (match synthesise_elims_type ctxt h elims with
       | Ok (V_Sigma (s, t)) ->
          Ok s
       | Ok (V_TyEq (V_Pi (s,t), V_Pi (s',t'))) ->
          Ok (V_TyEq (s',s))
       | Ok (V_TyEq (V_Sigma (s,t), V_Sigma (s',t'))) ->
          Ok (V_TyEq (s,s'))
       | Ok _ ->
          Error (`Msg "attempt to project from expression of non pair type")
       | Error msg ->
          Error msg)

  | Project (elims, `snd) ->
     (match synthesise_elims_type ctxt h elims with
       | Ok (V_Sigma (s, VB (_, t))) ->
          Ok (t (Evaluation.eval0 ctxt (Neutral (h, elims))))
       | Ok (V_TyEq (V_Pi (s, VB (x, t)), V_Pi (s', VB (x', t'))))
       | Ok (V_TyEq (V_Sigma (s, VB (x, t)), V_Sigma (s', VB (x', t')))) ->
          Ok (V_Pi (s, VB (x, fun vs ->
              V_Pi (s', VB (x', fun vs' ->
                  V_Pi (V_TmEq { s=vs; s_ty=s; t=vs'; t_ty=s' },
                        VB (x^"_"^x', fun _ ->
                            V_TyEq (t vs, t' vs'))))))))
       | Ok _ ->
          Error (`Msg "attempt to project from expression of non pair type")
       | Error msg ->
          Error msg)

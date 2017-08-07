type 'a binder = B of string * 'a

type term =
  { term_loc  : Location.t
  ; term_data : term_data
  }

and term_data =
  | Neutral of head * elims

  | Set

  | Pi of term * term binder
  | Lam of term binder

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

and head =
  { head_loc  : Location.t
  ; head_data : head_data
  }

and head_data =
  | Bound  of int
  | Free   of string
  | Coerce of { coercee  : term
              ; src_type : term
              ; tgt_type : term
              ; eq_proof : term
              }

and elims =
  { elims_loc  : Location.t
  ; elims_data : elims_data
  }

and elims_data =
  | Nil
  | App     of elims * term
  | If      of elims * term binder * term * term
  | Project of elims * [`fst | `snd]

let mk_elim elims_data =
  { elims_data; elims_loc = Location.generated }
let mk_term term_data =
  { term_data; term_loc = Location.generated }
let mk_head head_data =
  { head_data; head_loc = Location.generated }


module AlphaEquality = struct

  let binder k (B (_, t1)) (B (_, t2)) =
    k t1 t2

  let rec equal_term t1 t2 = match t1.term_data, t2.term_data with
    | Neutral (h1, es1), Neutral (h2, es2) ->
       equal_head h1 h2 && equal_elims es1 es2
    | Lam t1, Lam t2 ->
       binder equal_term t1 t2
    | Set, Set ->
       true
    | Pi (s1, t1), Pi (s2, t2)
    | Sigma (s1, t1), Sigma (s2, t2) ->
       equal_term s1 s2 && binder equal_term t1 t2
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
       binder equal_term ty_t ty_t' &&
       equal_term tm_x tm_x' &&
       equal_term tm_y tm_y' &&
       equal_term tm_e tm_e'
    | Refl, Refl
    | Coh,  Coh ->
       true
    | Funext e, Funext e' ->
       binder (binder (binder equal_term)) e e'
    | Irrel, Irrel ->
       true
    | _, _ ->
       false

  and equal_head h1 h2 = match h1.head_data, h2.head_data with
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

  and equal_elims e1 e2 = match e1.elims_data, e2.elims_data with
    | Nil, Nil ->
       true
    | App (es, t), App (es', t') ->
       equal_elims es es' && equal_term t t'
    | If (es, ty, tm_t, tm_f),
      If (es', ty', tm_t', tm_f') ->
       equal_elims es es' &&
       binder equal_term ty ty' &&
       equal_term tm_t tm_t' &&
       equal_term tm_f tm_f'
    | Project (es, dir), Project (es', dir') ->
       dir = dir' && equal_elims es es'
    | _, _ ->
       false

end

(**********************************************************************)
module type EXTENDABLE_CONTEXT = sig
  type t

  type value

  val extend : string -> value -> t -> string * t
end

module Scoping : sig
  val bind : string -> term -> term binder

  val bind3 : string -> string -> string -> term -> term binder binder binder

  val bind_anon : term -> term binder

  module Close (Ctxt : EXTENDABLE_CONTEXT) : sig
    val close : Ctxt.value -> term binder -> Ctxt.t -> string * term * Ctxt.t

    val close3 :
      Ctxt.value ->
      (string -> Ctxt.value) ->
      (string -> string -> Ctxt.value) ->
      term binder binder binder ->
      Ctxt.t ->
      string * string * string * term * Ctxt.t
  end
end = struct
  let binder k j = function
    | B (nm, t) -> B (nm, k (j+1) t)

  let traverse ~free ~bound j tm =
    let rec traverse_term j = function
      | {term_data=Neutral (head, elims)} as tm ->
         { tm with
             term_data = Neutral (traverse_head j head, traverse_elims j elims)
         }
      | {term_data = Lam t} as tm ->
         { tm with
             term_data = Lam (binder traverse_term j t)
         }
      | {term_data = Set} as tm ->
         tm
      | {term_data = Pi (s, t)} as tm ->
         { tm with
             term_data = Pi (traverse_term j s, binder traverse_term j t)
         }
      | {term_data = Sigma (s, t)} as tm ->
         { tm with
             term_data = Sigma (traverse_term j s, binder traverse_term j t)
         }
      | {term_data = Pair (t1, t2)} as tm ->
         { tm with
             term_data =  Pair (traverse_term j t1, traverse_term j t2)
         }
      | {term_data = TyEq (s, t)} as tm ->
         { tm with
             term_data = TyEq (traverse_term j s, traverse_term j t)
         }
      | {term_data = TmEq {tm1;ty1;tm2;ty2}} as tm ->
         { tm with
             term_data = TmEq { tm1 = traverse_term j tm1
                              ; ty1 = traverse_term j ty1
                              ; tm2 = traverse_term j tm2
                              ; ty2 = traverse_term j ty2
                              }
         }
      | {term_data = Bool | True | False} as tm ->
         tm
      | {term_data = Subst { ty_s; ty_t; tm_x; tm_y; tm_e }} as tm ->
         { tm with
             term_data = Subst { ty_s = traverse_term j ty_s
                               ; ty_t = binder traverse_term j ty_t
                               ; tm_x = traverse_term j tm_x
                               ; tm_y = traverse_term j tm_y
                               ; tm_e = traverse_term j tm_e
                               }
         }
      | {term_data = Refl | Coh} as tm ->
         tm
      | {term_data = Funext prf} as tm ->
         { tm with
             term_data = Funext (binder (binder (binder traverse_term)) j prf)
         }
      | {term_data = Irrel} ->
         failwith "internal error: attempt to bind in an erased proof term"

    and traverse_head j = function
      | { head_data = Bound i } as h ->
         { h with head_data = bound i j }
      | { head_data = Free nm } as h ->
         { h with head_data = free nm j }
      | { head_data = Coerce { coercee; src_type; tgt_type; eq_proof } } as h ->
         { h with
              head_data = 
                Coerce { coercee  = traverse_term j coercee
                       ; src_type = traverse_term j src_type
                       ; tgt_type = traverse_term j tgt_type
                       ; eq_proof = traverse_term j eq_proof
                       }
         }

    and traverse_elims j = function
      | { elims_data = Nil } as es ->
         { es with elims_data = Nil }
      | { elims_data = App (elims, tm) } as es ->
         { es with
             elims_data = App (traverse_elims j elims, traverse_term j tm)
         }
      | { elims_data = If (elims, ty, tm_t, tm_f) } as es ->
         { es with
             elims_data = If (traverse_elims j elims,
                              binder traverse_term j ty,
                              traverse_term j tm_t,
                              traverse_term j tm_f)
         }
      | { elims_data = Project (elims, component) } as es ->
         { es with
             elims_data = Project (traverse_elims j elims, component)
         }
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

  module Close (Ctxt : EXTENDABLE_CONTEXT) = struct
    let close v (B (nm, tm)) ctxt =
      let nm, ctxt = Ctxt.extend nm v ctxt in
      nm, close_term nm 0 tm, ctxt

    let close3 v1 v2 v3 (B (nm1, B (nm2, B (nm3, t)))) ctxt =
      let nm1, ctxt = Ctxt.extend nm1 v1 ctxt in
      let nm2, ctxt = Ctxt.extend nm2 (v2 nm1) ctxt in
      let nm3, ctxt = Ctxt.extend nm3 (v3 nm1 nm2) ctxt in
      nm1, nm2, nm3, close_term nm3 0 (close_term nm2 1 (close_term nm1 2 t)), ctxt
  end

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
     mk_term (Pi (reify_type s i, B (x, reify_type (t (var s i)) (i+1))))
  | V_Sigma (s, VB (x, t)) ->
     mk_term (Sigma (reify_type s i, B (x, reify_type (t (var s i)) (i+1))))
  | V_Set ->
     mk_term Set
  | V_Bool ->
     mk_term Bool
  | V_TyEq (s, t) ->
     mk_term (TyEq (reify_type s i, reify_type t i))
  | V_TmEq {s; s_ty; t; t_ty} ->
     mk_term (TmEq { tm1 = reify s_ty s i
                   ; ty1 = reify_type s_ty i
                   ; tm2 = reify t_ty t i
                   ; ty2 = reify_type t_ty i
                   })
  | V_Neutral (h, es) ->
     reify_neutral h es i
  | _ ->
     failwith "internal error: refiy_type -- not in canonical form"

and reify ty v i = match ty, v with
  | V_Pi (s, VB (_, t)), V_Lam (VB (x, body)) ->
     let v = var s i in
     mk_term (Lam (B (x, reify (t v) (body v) (i+1))))
  | V_Pi (s, VB (x, t)), f ->
     let v = var s i in
     mk_term (Lam (B (x, reify (t v) (apply f v) (i+1))))
  | V_Sigma (s, VB (_, t)), p ->
     mk_term (Pair (reify s (vfst p) i, reify (t (vfst p)) (vsnd p) i))
  | V_TyEq _, v
  | V_TmEq _, v       ->
     mk_term Irrel
  | V_Bool,   V_True  ->
     mk_term True
  | V_Bool,   V_False ->
     mk_term False
  | V_Set,    v ->
     reify_type v i
  | _, V_Neutral (h, es) ->
     reify_neutral h es i
  | _ ->
     failwith "internal error: reification failed"

and reify_neutral h es i : term = match h with
  | H_Var { shift; typ } ->
     let es, _ = reify_elims h typ es i in
     let h     = mk_head (Bound (i-shift-1)) in
     mk_term (Neutral (h, es))
  | H_Free { name; typ } ->
     let es, _ = reify_elims h typ es i in
     let h     = mk_head (Free name) in
     mk_term (Neutral (h, es))
  | H_Coe { coercee; src_type; tgt_type } ->
     let ty1_tm = reify_type src_type i in
     let ty2_tm = reify_type tgt_type i in
     if AlphaEquality.equal_term ty1_tm ty2_tm then
       reify src_type (eval_elims coercee es) i
     else
       let es, _ = reify_elims h tgt_type es i in
       let h = mk_head (Coerce { coercee  = reify src_type coercee i
                               ; src_type = ty1_tm
                               ; tgt_type = ty2_tm
                               ; eq_proof = mk_term Irrel })
       in
       mk_term (Neutral (h, es))

and reify_elims h ty es i = match es with
  | E_Nil ->
     mk_elim Nil, ty
  | E_App (es, v) ->
     (match reify_elims h ty es i with
       | es, V_Pi (s, VB (_, t)) ->
          mk_elim (App (es, reify s v i)), t v
       | _ ->
          failwith "internal error: type error reifying application")
  | E_If (es, VB (x, elim_ty), v_t, v_f) ->
     (match reify_elims h ty es i with
       | es', V_Bool ->
          mk_elim (If (es',
                       B (x, reify_type (elim_ty (var V_Bool i)) (i+1)),
                       reify (elim_ty V_True) v_t i,
                       reify (elim_ty V_False) v_f i)),
          elim_ty (V_Neutral (h, es))
       | _ ->
          failwith "internal error: type error reifying bool case switch")
  | E_Project (es, component) ->
     (match reify_elims h ty es i, component with
       | (reified_es, V_Sigma (s, _)), `fst ->
          mk_elim (Project (reified_es, `fst)), s
       | (reified_es, V_Sigma (s, VB (_, t))), `snd ->
          mk_elim (Project (reified_es, `snd)), t (V_Neutral (h, es))
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

  type nonrec value = value
  
  val empty : t

  val extend : string -> value -> t -> string * t

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

  type nonrec value = value
  
  let empty =
    { next_var = 0; entries = VarMap.empty }

  (* FIXME: what if we extend with a name that is already free in the
     term? *)
  let extend _varnm value ctxt =
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
    let rec eval tm env = match tm.term_data with
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

    and eval_head h env = match h.head_data with
      | Bound i -> List.nth env i (* FIXME: something better than lists? *)
      | Free nm ->
         (match Context.lookup_exn nm ctxt with
           | typ, None ->
              V_Neutral (H_Free { name = nm; typ }, E_Nil)
           | typ, Some defn ->
              defn)
      | Coerce { coercee; src_type; tgt_type } ->
         coerce (eval coercee env) (eval src_type env) (eval tgt_type env)

    and eval_elims scrutinee elims env = match elims.elims_data with
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

  let eval0 ctxt tm =
    evaluate ctxt tm []

  let eval1 ctxt (B (_, tm)) v =
    evaluate ctxt tm [v]
end
  
(******************************************************************************)
type error_message =
  [ `Type_mismatch of Location.t * term * term
  | `VarNotFound of Location.t * string
  | `MsgLoc of Location.t * string
  ]

module ScopeClose = Scoping.Close (Context)

let (>>=) result f = match result with
  | Ok x           -> f x
  | Error msg as x -> x

let rec is_type ctxt = function
  | { term_data = Set } ->
     Ok ()

  | { term_data = Bool } ->
     Ok ()

  | { term_data = Pi (s, t) } ->
     is_type ctxt s >>= fun () ->
     let _, t, ctxt = ScopeClose.close (Evaluation.eval0 ctxt s) t ctxt in
     is_type ctxt t

  | { term_data = Sigma (s, t) } ->
     is_type ctxt s >>= fun () ->
     let _, t, ctxt = ScopeClose.close (Evaluation.eval0 ctxt s) t ctxt in
     is_type ctxt t

  | { term_data = TyEq (s, t) } ->
     is_type ctxt s >>= fun () ->
     is_type ctxt t

  | { term_data = TmEq {tm1; ty1; tm2; ty2} } ->
     is_type ctxt ty1 >>= fun () ->
     is_type ctxt ty2 >>= fun () ->
     let ty1 = Evaluation.eval0 ctxt ty1 in
     let ty2 = Evaluation.eval0 ctxt ty2 in
     has_type ctxt ty1 tm1 >>= fun () ->
     has_type ctxt ty2 tm2 >>= fun () ->
     Ok ()

  | { term_data = Neutral (h, es); term_loc } ->
     (synthesise_elims_type ctxt h es >>= function
       | V_Set ->
          Ok ()
       | _ ->
          Error (`MsgLoc (term_loc, "expecting a value of type 'Set'")))

  | { term_loc } ->
     Error (`MsgLoc (term_loc, "Not a type"))

and has_type ctxt ty tm = match ty, tm with
  | ty, { term_data = Neutral (h, elims); term_loc } ->
     synthesise_elims_type ctxt h elims >>= fun ty' ->
     let ty = reify_type ty 0 in
     let ty' = reify_type ty' 0 in
     if AlphaEquality.equal_term ty ty' then
       Ok ()
     else
       Error (`Type_mismatch (term_loc, ty, ty'))

  | V_Pi (s, VB (_, t)), { term_data = Lam tm } ->
     let x, tm, ctxt = ScopeClose.close s tm ctxt in
     has_type ctxt (t (free x s)) tm

  | V_Pi _, { term_loc } ->
     Error (`MsgLoc (term_loc, "This term is expected to be a function, but isn't"))

  | V_Sigma (s, VB (_, t)), { term_data = Pair (tm_s, tm_t) } ->
     has_type ctxt s tm_s >>= fun () ->
     let tm_s = Evaluation.eval0 ctxt tm_s in
     has_type ctxt (t tm_s) tm_t

  | V_Sigma _, { term_loc } ->
     Error (`MsgLoc (term_loc, "This term is expected to be a pair, but isn't"))

  | V_Set, { term_data = Bool } ->
     Ok ()

  | V_Set, { term_data = Pi (s, t) } ->
     has_type ctxt V_Set s >>= fun () ->
     let _, t, ctxt = ScopeClose.close (Evaluation.eval0 ctxt s) t ctxt in
     has_type ctxt V_Set t

  | V_Set, { term_data = Sigma (s, t) } ->
     has_type ctxt V_Set s >>= fun () ->
     let _, t, ctxt = ScopeClose.close (Evaluation.eval0 ctxt s) t ctxt in
     has_type ctxt V_Set t

  | V_Set, { term_data = TyEq (s, t) } ->
     is_type ctxt s >>= fun () ->
     is_type ctxt t

  | V_Set, { term_data = TmEq {tm1; ty1; tm2; ty2} } ->
     is_type ctxt ty1 >>= fun () ->
     is_type ctxt ty2 >>= fun () ->
     let ty1 = Evaluation.eval0 ctxt ty1 in
     let ty2 = Evaluation.eval0 ctxt ty2 in
     has_type ctxt ty1 tm1 >>= fun () ->
     has_type ctxt ty2 tm2

  | V_Set, { term_loc } ->
     Error (`MsgLoc (term_loc, "This term is expected to be a code for a type, but isn't"))

  | V_Bool, { term_data = True | False } ->
     Ok ()

  | V_Bool, { term_loc } ->
     Error (`MsgLoc (term_loc, "This term is expected to be a boolean, but isn't"))

  | V_TyEq (ty1, ty2),
    { term_data = Subst { ty_s; ty_t; tm_x; tm_y; tm_e }; term_loc } ->
     is_type ctxt ty_s >>= fun () ->
     let ty_s = Evaluation.eval0 ctxt ty_s in
     (let _, ty_t, ctxt = ScopeClose.close ty_s ty_t ctxt in is_type ctxt ty_t) >>= fun () ->
     let ty_t = Evaluation.eval1 ctxt ty_t in
     has_type ctxt ty_s tm_x >>= fun () ->
     has_type ctxt ty_s tm_y >>= fun () ->
     let tm_x = Evaluation.eval0 ctxt tm_x in
     let tm_y = Evaluation.eval0 ctxt tm_y in
     let ty   =
       V_TmEq { s = tm_x; s_ty = ty_s; t = tm_y; t_ty = ty_s }
     in
     has_type ctxt ty tm_e >>= fun () ->
     if equal_types (ty_t tm_x) ty1 && equal_types (ty_t tm_y) ty2 then
       Ok ()
     else
       Error (`MsgLoc (term_loc, "type mismatch in subst"))

  | V_TyEq (ty1, ty2),
    { term_data = Refl; term_loc } ->
     if equal_types ty1 ty2 then
       Ok ()
     else
       Error (`MsgLoc (term_loc, "types not equal in refl"))

  | V_TyEq _, { term_loc } ->
     Error (`MsgLoc (term_loc, "This term is expected to be a type equality, but isn't"))

  | V_TmEq { s; s_ty; t; t_ty }, { term_data = Refl; term_loc } ->
     (* FIXME: "Using 'Refl' as a proof of the equality 'XXX' failed
        because the types are not equal/terms are not judgementally
        equal." *)
     if equal_types s_ty t_ty then
       (if equal_terms s t s_ty then
          Ok ()
        else
          Error (`MsgLoc (term_loc, "terms not equal in refl")))
     else
       Error (`MsgLoc (term_loc, "types not equal in refl"))

  | V_TmEq { s=tm_f1; s_ty=V_Pi (s1, VB (_, t1))
           ; t=tm_f2; t_ty=V_Pi (s2, VB (_, t2))},
    { term_data = Funext proof } ->
     let x1, x2, _, proof, ctxt =
       ScopeClose.close3
         s1
         (fun _ -> s2)
         (fun x1 x2 ->
            let x1v = free x1 s1 in
            let x2v = free x2 s2 in
            V_TmEq {s=x1v; s_ty=s2; t=x2v; t_ty=s2})
         proof
         ctxt
     in
     let x1v = free x1 s1 in
     let x2v = free x2 s2 in
     let reqd_ty  =
       V_TmEq { s    = apply tm_f1 x1v
              ; s_ty = t1 x1v
              ; t    = apply tm_f2 x2v
              ; t_ty = t2 x2v
              }
     in
     has_type ctxt reqd_ty proof

  | V_TmEq {s; s_ty; t; t_ty}, { term_data = Coh; term_loc } ->
     let t' =
       V_Neutral (H_Coe { coercee = s; src_type = s_ty; tgt_type = t_ty }, E_Nil)
     in
     if equal_terms t t' t_ty then
       Ok ()
     else
       Error (`MsgLoc (term_loc, "invalid Coh"))

  | V_TmEq _, { term_loc } ->
     Error (`MsgLoc (term_loc, "This term is expected to be a term equality, but isn't"))

  | (V_True | V_False | V_Lam _ | V_Pair _ | V_Irrel | V_Neutral _), _ ->
     failwith "internal error: has_type: attempting to check canonical term aganst non canonical type"

and synthesise_head_type ctxt = function
  | { head_data = Bound _ } ->
     failwith "internal error: bound variable has got free"

  | { head_data = Free nm; head_loc } ->
     (match Context.lookup nm ctxt with
       | Ok ty ->
          Ok ty
       | Error (`VarNotFound nm) ->
          Error (`VarNotFound (head_loc, nm)))

  | { head_data = Coerce { coercee; src_type; tgt_type; eq_proof } } ->
     is_type ctxt src_type >>= fun () ->
     is_type ctxt tgt_type >>= fun () ->
     let ty1 = Evaluation.eval0 ctxt src_type in
     let ty2 = Evaluation.eval0 ctxt tgt_type in
     has_type ctxt ty1 coercee >>= fun () ->
     has_type ctxt (V_TyEq (ty1, ty2)) eq_proof >>= fun () ->
     Ok ty2

and synthesise_elims_type ctxt h = function
  | { elims_data = Nil } ->
     synthesise_head_type ctxt h

  | { elims_data = App (elims, tm); elims_loc } ->
     (synthesise_elims_type ctxt h elims >>= function
       | V_Pi (s, VB (_, t)) ->
          has_type ctxt s tm >>= fun () ->
          Ok (t (Evaluation.eval0 ctxt tm))
       | _ ->
          (* error: attenpt to apply 'elims' to 'tm', but elims has
             type 'bloo' and cannot be used as a function. *)
          Error (`MsgLoc (elims_loc, "attempt to apply non function")))

  | { elims_data = If (elims, elim_ty, tm_t, tm_f); elims_loc } ->
     (synthesise_elims_type ctxt h elims >>= function
       | V_Bool ->
          (let _, elim_ty, ctxt = ScopeClose.close V_Bool elim_ty ctxt in
           is_type ctxt elim_ty)
          >>= fun () ->
          let ty = Evaluation.eval1 ctxt elim_ty in
          has_type ctxt (ty V_True) tm_t >>= fun () ->
          has_type ctxt (ty V_False) tm_f >>= fun () ->
          Ok (ty (Evaluation.eval0 ctxt (mk_term (Neutral (h, elims)))))
       | _ ->
          Error (`MsgLoc (elims_loc, "attempt to eliminate non boolean")))

  | { elims_data = Project (elims, `fst); elims_loc } ->
     (synthesise_elims_type ctxt h elims >>= function
       | V_Sigma (s, t) ->
          Ok s
       | V_TyEq (V_Pi (s,t), V_Pi (s',t')) ->
          Ok (V_TyEq (s',s))
       | V_TyEq (V_Sigma (s,t), V_Sigma (s',t')) ->
          Ok (V_TyEq (s,s'))
       | _ ->
          Error (`MsgLoc (elims_loc, "attempt to project from expression of non pair type")))

  | { elims_data = Project (elims, `snd); elims_loc } ->
     (synthesise_elims_type ctxt h elims >>= function
       | V_Sigma (s, VB (_, t)) ->
          Ok (t (Evaluation.eval0 ctxt (mk_term (Neutral (h, elims)))))
       | V_TyEq (V_Pi (s, VB (x, t)), V_Pi (s', VB (x', t')))
       | V_TyEq (V_Sigma (s, VB (x, t)), V_Sigma (s', VB (x', t'))) ->
          Ok (V_Pi (s, VB (x, fun vs ->
              V_Pi (s', VB (x', fun vs' ->
                  V_Pi (V_TmEq { s=vs; s_ty=s; t=vs'; t_ty=s' },
                        VB (x^"_"^x', fun _ ->
                            V_TyEq (t vs, t' vs'))))))))
       | _ ->
          Error (`MsgLoc (elims_loc, "attempt to project from expression of non pair type")))

open Syntax

(* Semantic interpretation *)

type shift = int

type value =
  | V_Neutral of v_head * v_elims
  | V_Lam     of value v_binder
  | V_Set
  | V_Nat
  | V_Zero
  | V_Succ    of value
  | V_QuotType  of value * value
  | V_QuotIntro of value
  | V_Pi      of value * value v_binder
  | V_Sigma   of value * value v_binder
  | V_Pair    of value * value
  | V_TagType of tag_set
  | V_Tag     of tag
  | V_TyEq    of value * value
  | V_TmEq    of { s : value; s_ty : value; t : value; t_ty : value }
  | V_Irrel

and 'a v_binder =
  | VB of string * (value -> 'a)

and v_elims =
  | E_Nil
  | E_App of v_elims * value
  | E_Project of v_elims * [`fst|`snd]
  | E_ElimNat of v_elims * value v_binder * value * value v_binder v_binder
  | E_ElimQ   of v_elims * value v_binder * value v_binder
  | E_ElimTag of v_elims * value v_binder * value tag_map

and v_head =
  | H_Var of { shift : shift; typ : value }
  | H_Free_local of { name  : string; typ : value }
  | H_Free_global of { name  : string; typ : value; defn : value option }
  | H_Coe of { coercee  : value
             ; src_type : value
             ; tgt_type : value
             }

let inst_binder (VB (_, f)) v = f v

let apply v1 v2 = match v1 with
  | V_Lam v           -> inst_binder v v2
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

let elimnat ty v_z v_s =
  let rec natrec = function
    | V_Zero   -> v_z
    | V_Succ n -> inst_binder (inst_binder v_s n) (natrec n)
    | V_Neutral (h, es) ->
       V_Neutral (h, E_ElimNat (es, ty, v_z, v_s))
    | _ ->
       failwith "internal error: type error in Nat elimination"
  in
  natrec

let elimq ty v = function
  | V_QuotIntro a -> inst_binder v a
  | V_Neutral (h, es) ->
     V_Neutral (h, E_ElimQ (es, ty, v))
  | _ ->
     failwith "internal error: type error in quotient value elimination"

let elimtag ty clauses = function
  | V_Tag tag -> TagMap.find tag clauses
  | V_Neutral (h, es) ->
     V_Neutral (h, E_ElimTag (es, ty, clauses))
  | _ ->
     failwith "internal error: type error in Tag elimination"

let rec eval_elims t = function
  | E_Nil -> t
  | E_App (es, v) ->
     apply (eval_elims t es) v
  | E_Project (es, `fst) ->
     vfst (eval_elims t es)
  | E_Project (es, `snd) ->
     vsnd (eval_elims t es)
  | E_ElimNat (es, ty, v_z, v_s) ->
     elimnat ty v_z v_s (eval_elims t es)
  | E_ElimQ (es, ty, v) ->
     elimq ty v (eval_elims t es)
  | E_ElimTag (es, ty, clauses) ->
     elimtag ty clauses (eval_elims t es)

let rec expand_value = function
  | V_Neutral (H_Free_global { defn = Some defn }, es) ->
     expand_value (eval_elims defn es)
  | ty ->
     ty


let var ty i =
  V_Neutral (H_Var { shift = i; typ = ty }, E_Nil)

let free x ty =
  V_Neutral (H_Free_local { name = x; typ = ty }, E_Nil)

let (@->) s t = V_Pi (s, VB ("x", fun _ -> t))

let rec coerce v src tgt = match v, expand_value src, expand_value tgt with
  | v, V_Set,  V_Set  -> v
  | n, V_Nat, V_Nat -> n
  | t, V_TagType tags1, V_TagType tags2 when TagSet.equal tags1 tags2 ->
     t
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
  | c, V_QuotType (ty1, r1), V_QuotType (ty2, r2) ->
     elimq
       (VB ("x", fun _ -> V_QuotType (ty2, r2)))
       (VB ("x", fun x -> V_QuotIntro (coerce x ty1 ty2)))
       c
  | _, V_TyEq _, V_TyEq _
  | _, V_TmEq _, V_TmEq _
  | _, V_Neutral _, _
  | _, _, V_Neutral _ ->
     V_Neutral (H_Coe { coercee = v; src_type = src; tgt_type = tgt }, E_Nil)
  | _ ->
     (* FIXME: ought to be a suspended falsity elimination *)
     V_Neutral (H_Coe { coercee = v; src_type = src; tgt_type = tgt }, E_Nil)

(**********************************************************************)
(* FIXME: equality test rather than reify to term and check for alpha
   equality? This would mean that we wouldn't need to use the 'Irrel'
   constructor. *)

let reifiers ~eta_expand =
  let rec reify_type v i = match v with
    | V_Pi (s, VB (x, t)) ->
       mk_term (Pi (reify_type s i, B (x, reify_type (t (var s i)) (i+1))))
    | V_Sigma (s, VB (x, t)) ->
       mk_term (Sigma (reify_type s i, B (x, reify_type (t (var s i)) (i+1))))
    | V_Set ->
       mk_term Set
    | V_Nat ->
       mk_term Nat
    | V_QuotType (ty, r) ->
       mk_term (QuotType (reify_type ty i, reify (ty @-> ty @-> V_Set) r i))
    | V_TagType tags ->
       mk_term (TagType tags)
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
       failwith "internal error: reify_type -- not in canonical form"

  and reify ty v i = match expand_value ty, v with
    | V_Pi (s, VB (_, t)), V_Lam (VB (x, body)) ->
       let v = var s i in
       mk_term (Lam (B (x, reify (t v) (body v) (i+1))))
    | V_Pi (s, VB (x, t)), f ->
       let v = var s i in
       mk_term (Lam (B (x, reify (t v) (apply f v) (i+1))))
    | V_Sigma (s, VB (_, t)), p when eta_expand ->
       mk_term (Pair (reify s (vfst p) i, reify (t (vfst p)) (vsnd p) i))
    | V_Sigma (s, VB (_, t)), V_Pair (a, b) ->
       mk_term (Pair (reify s a i, reify (t a) b i))
    | V_TyEq _, v
    | V_TmEq _, v ->
       mk_term Irrel
    | V_Nat, V_Zero ->
       mk_term Zero
    | V_Nat, V_Succ n ->
       mk_term (Succ (reify V_Nat n i))
    | V_TagType _, V_Tag tag ->
       mk_term (Tag tag)
    | V_Set, v ->
       reify_type v i
    | V_QuotType (t, _), V_QuotIntro v ->
       mk_term (QuotIntro (reify t v i))
    | _, V_Neutral (h, es) ->
       reify_neutral h es i
    | _ ->
       failwith "internal error: reification failed"

  and reify_neutral h es i : term = match h with
    | H_Var { shift; typ } ->
       let es, _ = reify_elims h typ es i in
       let h     = mk_head (Bound (i-shift-1)) in
       mk_term (Neutral (h, es, None))
    | H_Free_local { name; typ } ->
       let es, _ = reify_elims h typ es i in
       let h     = mk_head (Free_local name) in
       mk_term (Neutral (h, es, None))
    | H_Free_global { name; typ; defn = None } ->
       let es, _ = reify_elims h typ es i in
       let h     = mk_head (Free_global name) in
       mk_term (Neutral (h, es, None))
    | H_Free_global { name; typ; defn = Some defn } ->
       let es', ty = reify_elims h typ es i in
       let h       = mk_head (Free_global name) in
       let reduced = lazy (reify ty (eval_elims defn es) i) in
       mk_term (Neutral (h, es', Some reduced))
    | H_Coe { coercee; src_type; tgt_type } ->
       let es_tm, ty = reify_elims h tgt_type es i in
       let ty1_tm = reify_type src_type i in
       let ty2_tm = reify_type tgt_type i in
       if Syntax.alpha_eq ty1_tm ty2_tm then
         reify ty (eval_elims coercee es) i
       else
         let h = mk_head (Coerce { coercee  = reify src_type coercee i
                                 ; src_type = ty1_tm
                                 ; tgt_type = ty2_tm
                                 ; eq_proof = mk_term Irrel })
         in
         mk_term (Neutral (h, es_tm, None))

  (* FIXME: this unfolds too much??? *)
  and reify_elims h ty es i =
    let tm, ty = reify_elims_inner h ty es i in
    tm, expand_value ty

  and reify_elims_inner h ty es i = match es with
    | E_Nil ->
       mk_elim Nil, ty
    | E_App (es, v) ->
       (match reify_elims h ty es i with
         | es, V_Pi (s, VB (_, t)) ->
            mk_elim (App (es, reify s v i)), t v
         | _ ->
            failwith "internal error: type error reifying application")
    | E_Project (es, component) ->
       (* Note: we don't need to check for the projections from type
          equalities cases here because they will have been erased
          during evaluation. *)
       (match reify_elims h ty es i, component with
         | (reified_es, V_Sigma (s, _)), `fst ->
            mk_elim (Project (reified_es, `fst)), s
         | (reified_es, V_Sigma (s, VB (_, t))), `snd ->
            mk_elim (Project (reified_es, `snd)), t (V_Neutral (h, es))
         | _ ->
            failwith "internal error: type error reifying a projection")
    | E_ElimNat (es, VB (x, elim_ty), v_z, v_s) ->
       (match reify_elims h ty es i with
         | es', V_Nat ->
            mk_elim (ElimNat (es',
                              B (x, reify_type (elim_ty (var V_Nat i)) (i+1)),
                              reify (elim_ty V_Zero) v_z i,
                              let VB (n, v_s) = v_s in
                              let var_n = var V_Nat i in
                              let VB (p, v_s) = v_s var_n in
                              let var_p = var (elim_ty var_n) (i+1) in
                              B (n, B (p, reify (elim_ty var_n) (v_s var_p) (i+2))))),
            elim_ty (V_Neutral (h, es))
         | _ ->
            failwith "internal error: type error reifying bool case switch")
    | E_ElimQ (es, VB (x, elim_ty), VB (a, v)) ->
       (match reify_elims h ty es i with
         | es', (V_QuotType (s, _) as ty') ->
            mk_elim (ElimQ (es',
                            B (x, reify_type (elim_ty (var ty' i)) (i+1)),
                            B (a, reify (elim_ty (V_QuotIntro (var s i))) (v (var s i)) (i+1)),
                            B ("x1", B ("x2", B ("xr", mk_term Irrel))))),
            elim_ty (V_Neutral (h, es))
         | _ ->
            failwith "internal error: type error reifying quotient elim")
    | E_ElimTag (es, VB (x, elim_ty), clauses) ->
       (match reify_elims h ty es i with
         | es', (V_TagType _ as ty') ->
            mk_elim (ElimTag (es',
                              B (x, reify_type (elim_ty (var ty' i)) (i+1)),
                              TagMap.mapi (fun tag v -> reify (elim_ty (V_Tag tag)) v i) clauses)),
            elim_ty (V_Neutral (h, es))
         | _ ->
            failwith "internal error: type error reifying tag elim")
  in
  reify_type, reify

let reify_type, reify = reifiers ~eta_expand:true
let reify_type_small, reify_small = reifiers ~eta_expand:false

let equal_types ty1 ty2 =
  let ty1 = reify_type ty1 0 in
  let ty2 = reify_type ty2 0 in
  Syntax.alpha_eq ty1 ty2

let equal_terms tm1 tm2 ty =
  let tm1 = reify ty tm1 0 in
  let tm2 = reify ty tm2 0 in
  Syntax.alpha_eq tm1 tm2

(**********************************************************************)
(* Contexts *)

(* FIXME: contexts ought to distinguish between 'global' (i.e bindings
   outwith the current term), and 'local'. *)

module Context =
  Context.Make (struct
    type ty = value
    type tm = value
    let mk_free = free
  end)

(******************************************************************************)
(* Evaluation: injection into the semantic 'value' domain. *)
module Evaluation : sig
  val eval0 : Context.t -> term -> value
  val eval1 : Context.t -> term binder -> value -> value
end = struct
  let binder k (B (nm, tm)) env =
    VB (nm, fun v -> k tm (v::env))

  let evaluate ctxt tm =
    let rec eval tm env = match tm.term_data with
      | Neutral (h, es, _) -> eval_elims (eval_head h env) es env
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
      | Nat   -> V_Nat
      | Zero  -> V_Zero
      | Succ t -> V_Succ (eval t env)
      | TagType tags -> V_TagType tags
      | Tag tag      -> V_Tag tag
      | QuotType (ty, r) ->
         V_QuotType (eval ty env, eval r env)
      | QuotIntro tm ->
         V_QuotIntro (eval tm env)

      | Subst _ | Coh _ | Funext _ | Refl | Irrel | SameClass _ ->
         V_Irrel

    and eval_head h env = match h.head_data with
      | Bound i ->
         List.nth env i (* FIXME: something better than lists? *)
      | Free_local nm ->
         (match Context.lookup_exn nm ctxt with
           | typ, None ->
              V_Neutral (H_Free_local { name = nm; typ }, E_Nil)
           | typ, Some defn ->
              defn)
      | Free_global nm ->
         let typ, defn = Context.lookup_exn nm ctxt in
         V_Neutral (H_Free_global { name = nm; typ; defn }, E_Nil)
      | Coerce { coercee; src_type; tgt_type } ->
         coerce (eval coercee env) (eval src_type env) (eval tgt_type env)

    and eval_elims scrutinee elims env = match elims.elims_data with
      | Nil ->
         scrutinee
      | App (elims, tm) ->
         apply (eval_elims scrutinee elims env) (eval tm env)
      | Project (elims, `fst) ->
         vfst (eval_elims scrutinee elims env)
      | Project (elims, `snd) ->
         vsnd (eval_elims scrutinee elims env)
      | ElimNat (elims, ty, tm_z, tm_s) ->
         elimnat
           (binder eval ty env)
           (eval tm_z env)
           (binder (binder eval) tm_s env)
           (eval_elims scrutinee elims env)
      | ElimQ (elims, ty, tm, _) ->
         elimq
           (binder eval ty env)
           (binder eval tm env)
           (eval_elims scrutinee elims env)
      | ElimTag (elims, ty, clauses) ->
         elimtag
           (binder eval ty env)
           (TagMap.map (fun tm -> eval tm env) clauses)
           (eval_elims scrutinee elims env)
    in
    eval tm

  let eval0 ctxt tm =
    evaluate ctxt tm []

  let eval1 ctxt (B (_, tm)) v =
    evaluate ctxt tm [v]
end

(******************************************************************************)
type error_message =
  | Term_is_not_a_type of Location.t
  | Type_mismatch of
      { loc         : Location.t
      ; ctxt        : Context.t
      ; computed_ty : term
      ; expected_ty : term }
  | Term_is_not_a_function of Location.t
  | Term_is_not_a_pair of Location.t
  | Term_is_not_a_small_type of Location.t
  | Term_is_not_a_natural of Location.t
  | Term_is_not_an_equiv_class of Location.t
  | Term_is_not_a_valid_tag of Location.t * tag_set
  | Term_is_not_a_type_equality of Location.t
  | Term_is_not_a_term_equality of Location.t
  | Types_not_equal of
      { loc  : Location.t
      ; ctxt : Context.t
      ; ty1  : term
      ; ty2  : term }
  | Terms_not_equal of
      { loc  : Location.t
      ; ctxt : Context.t
      ; tm1  : Syntax.term
      ; tm2  : Syntax.term
      ; ty   : Syntax.term
      }
  | BadSubst of
      { loc  : Location.t
      ; ctxt : Context.t
      ; desired_eq : Syntax.term * Syntax.term
      ; proved_eq  : Syntax.term * Syntax.term
      }
  | BadFunext of
      { loc  : Location.t
      ; ctxt : Context.t
      ; ty   : Syntax.term
      }
  | BadCoherence of
      { loc  : Location.t
      ; ctxt : Context.t
      ; ty   : Syntax.term
      }
  | BadSameClass of
      { loc  : Location.t
      ; ctxt : Context.t
      ; ty   : Syntax.term
      }
  | VarNotFound of Location.t * string
  | BadApplication of
      { loc     : Location.t
      ; arg_loc : Location.t
      ; ctxt    : Context.t
      ; ty      : term
      }
  | BadProject of
      { loc : Location.t
      ; hd_loc : Location.t
      ; ctxt   : Context.t
      ; ty     : term
      }
  | BadNatElim of
      { loc    : Location.t
      ; hd_loc : Location.t
      ; ctxt   : Context.t
      ; ty     : term
      }
  | BadQuotElim of
      { loc    : Location.t
      ; hd_loc : Location.t
      ; ctxt   : Context.t
      ; ty     : term
      }
  | BadTagElim of
      { loc    : Location.t
      ; hd_loc : Location.t
      ; ctxt   : Context.t
      ; ty     : term
      }
  | IncorrectTags of
      { loc         : Location.t
      ; hd_loc      : Location.t
      ; unmatched   : tag_set
      ; unmatchable : tag_set
      }

module ScopeClose = Scoping.Close (Context)

let reword_error rewriter = function
  | Ok a      -> Ok a
  | Error err -> Error (rewriter err)

let (>>=) result f = match result with
  | Ok x         -> f x
  | Error _ as x -> x

let rec is_type ctxt = function
  | { term_data = Set } ->
     Ok ()

  | { term_data = Nat } ->
     Ok ()

  | { term_data = Pi (s, t) } ->
     is_type ctxt s >>= fun () ->
     let _, t, ctxt = ScopeClose.close (Evaluation.eval0 ctxt s) t ctxt in
     is_type ctxt t

  | { term_data = Sigma (s, t) } ->
     is_type ctxt s >>= fun () ->
     let _, t, ctxt = ScopeClose.close (Evaluation.eval0 ctxt s) t ctxt in
     is_type ctxt t

  | { term_data = QuotType (ty, r) } ->
     is_type ctxt ty >>= fun () ->
     let ty = Evaluation.eval0 ctxt ty in
     has_type ctxt (ty @-> ty @-> V_Set) r

  | { term_data = TagType tags } ->
     Ok ()

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

  | { term_data = Neutral (h, es, _); term_loc } ->
     (synthesise_elims_type ctxt h es >>= function
       | V_Set ->
          Ok ()
       | ty ->
          let computed_ty = reify_type_small ty 0 in
          let expected_ty = reify_type_small V_Set 0 in
          Error (Type_mismatch { loc = term_loc; ctxt; computed_ty; expected_ty }))

  | { term_loc } ->
     Error (Term_is_not_a_type term_loc)

and has_type ctxt ty tm = match expand_value ty, tm with
  | ty, { term_data = Neutral (h, elims, _); term_loc } ->
     synthesise_elims_type ctxt h elims >>= fun ty' ->
     if equal_types ty ty' then
       Ok ()
     else
       let expected_ty  = reify_type_small ty 0 in
       let computed_ty = reify_type_small ty' 0 in
       Error (Type_mismatch { loc = term_loc
                            ; ctxt; computed_ty; expected_ty })

  | V_Pi (s, VB (_, t)), { term_data = Lam tm } ->
     let x, tm, ctxt = ScopeClose.close s tm ctxt in
     has_type ctxt (t x) tm

  | V_Pi _, { term_loc } ->
     Error (Term_is_not_a_function term_loc)

  | V_Sigma (s, VB (_, t)), { term_data = Pair (tm_s, tm_t) } ->
     has_type ctxt s tm_s >>= fun () ->
     let tm_s = Evaluation.eval0 ctxt tm_s in
     has_type ctxt (t tm_s) tm_t

  | V_Sigma _, { term_loc } ->
     Error (Term_is_not_a_pair term_loc)

  | V_Set, { term_data = Nat } ->
     Ok ()

  | V_Set, { term_data = Pi (s, t) } ->
     has_type ctxt V_Set s >>= fun () ->
     let _, t, ctxt = ScopeClose.close (Evaluation.eval0 ctxt s) t ctxt in
     has_type ctxt V_Set t

  | V_Set, { term_data = Sigma (s, t) } ->
     has_type ctxt V_Set s >>= fun () ->
     let _, t, ctxt = ScopeClose.close (Evaluation.eval0 ctxt s) t ctxt in
     has_type ctxt V_Set t

  | V_Set, { term_data = QuotType (ty, r) } ->
     has_type ctxt V_Set ty >>= fun () ->
     let ty = Evaluation.eval0 ctxt ty in
     has_type ctxt (ty @-> ty @-> V_Set) r

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

  | V_Set, { term_data = TagType tags } ->
     Ok ()

  | V_Set, { term_loc } ->
     Error (Term_is_not_a_small_type term_loc)

  | V_Nat, { term_data = Zero } ->
     Ok ()
  | V_Nat, { term_data = Succ n } ->
     has_type ctxt V_Nat n
  | V_Nat, { term_loc } ->
     Error (Term_is_not_a_natural term_loc)

  | V_QuotType (ty, _), { term_data = QuotIntro tm } ->
     has_type ctxt ty tm
  | V_QuotType (ty, _), { term_loc } ->
     Error (Term_is_not_an_equiv_class term_loc)

  | V_TagType tags, { term_data = Tag tag; term_loc } ->
     if TagSet.mem tag tags then
       Ok ()
     else
       Error (Term_is_not_a_valid_tag (term_loc, tags))

  | V_TagType tags, { term_loc } ->
     Error (Term_is_not_a_valid_tag (term_loc, tags))

  | V_TyEq (ty1, ty2), { term_data = Subst { ty_s; ty_t; tm_x; tm_y; tm_e } } ->
     is_type ctxt ty_s >>= fun () ->
     let ty_s = Evaluation.eval0 ctxt ty_s in
     (let _, ty_t, ctxt = ScopeClose.close ty_s ty_t ctxt in is_type ctxt ty_t)
     >>= fun () ->
     let ty_t = Evaluation.eval1 ctxt ty_t in
     has_type ctxt ty_s tm_x >>= fun () ->
     has_type ctxt ty_s tm_y >>= fun () ->
     let tm_x = Evaluation.eval0 ctxt tm_x in
     let tm_y = Evaluation.eval0 ctxt tm_y in
     let ty   = V_TmEq { s = tm_x; s_ty = ty_s; t = tm_y; t_ty = ty_s } in
     has_type ctxt ty tm_e >>= fun () ->
     if equal_types (ty_t tm_x) ty1 && equal_types (ty_t tm_y) ty2 then
       Ok ()
     else
       let desd_ty1 = reify_type_small ty1 0 in
       let desd_ty2 = reify_type_small ty2 0 in
       let prvd_ty1 = reify_type_small (ty_t tm_x) 0 in
       let prvd_ty2 = reify_type_small (ty_t tm_y) 0 in
       Error (BadSubst { loc=tm.term_loc; ctxt
                       ; desired_eq = (desd_ty1, desd_ty2)
                       ; proved_eq  = (prvd_ty1, prvd_ty2)
                       })

  | V_TyEq (ty1, ty2),
    { term_data = Refl; term_loc } ->
     if equal_types ty1 ty2 then
       Ok ()
     else
       let ty1 = reify_type_small ty1 0 in
       let ty2 = reify_type_small ty2 0 in
       Error (Types_not_equal { loc = term_loc; ctxt; ty1; ty2 })

  | V_TyEq _, { term_loc } ->
     Error (Term_is_not_a_type_equality term_loc)

  | V_TmEq { s; s_ty; t; t_ty }, { term_data = Refl; term_loc } ->
     if equal_types s_ty t_ty then
       (if equal_terms s t s_ty then
          Ok ()
        else
          let s = reify_small s_ty s 0 in
          let t = reify_small s_ty t 0 in
          let ty = reify_type_small s_ty 0 in
          Error (Terms_not_equal { loc = term_loc; ctxt; tm1 = s; tm2 = t; ty}))
     else
       let s_ty = reify_type_small s_ty 0 in
       let t_ty = reify_type_small t_ty 0 in
       Error (Types_not_equal { loc = term_loc; ctxt; ty1 = s_ty; ty2 = t_ty})

  | V_TmEq { s=tm_f1; s_ty; t=tm_f2; t_ty} as ty, { term_data = Funext proof } ->
     (match expand_value s_ty, expand_value t_ty with
       | V_Pi (s1, VB (_, t1)), V_Pi (s2, VB (_, t2)) ->
          let x1, x2, _, proof, ctxt =
            ScopeClose.close3
              s1
              (fun _ -> s2)
              (fun x1 x2 ->
                 V_TmEq {s=x1; s_ty=s2; t=x2; t_ty=s2})
              proof
              ctxt
          in
          let reqd_ty =
            V_TmEq { s    = apply tm_f1 x1
                   ; s_ty = t1 x1
                   ; t    = apply tm_f2 x2
                   ; t_ty = t2 x2
                   }
          in
          has_type ctxt reqd_ty proof
       | _ ->
          let ty = reify_type_small ty 0 in
          Error (BadFunext { loc = tm.term_loc; ctxt; ty }))

  | V_TmEq {s; s_ty; t; t_ty}, { term_data = Coh prf; term_loc } ->
     has_type ctxt (V_TyEq (s_ty, t_ty)) prf >>= fun () ->
     if equal_terms t (coerce s s_ty t_ty) t_ty then
       Ok ()
     else
       let ty = reify_type_small ty 0 in
       Error (BadCoherence { loc = term_loc; ctxt; ty })

  | V_TmEq { s; s_ty; t; t_ty }, { term_data = SameClass prf; term_loc } ->
     let error_when_false flag =
       if flag then Ok ()
       else
         let ty = reify_type_small ty 0 in
         Error (BadSameClass { loc = term_loc; ctxt; ty })
     in
     (match expand_value s,
            expand_value s_ty,
            expand_value t,
            expand_value t_ty
      with
       | V_QuotIntro a1,
         V_QuotType (ty1, r1),
         V_QuotIntro a2,
         V_QuotType (ty2, r2) ->
          error_when_false (equal_types ty1 ty2)
          >>= fun () ->
          error_when_false (equal_terms r1 r2 (ty1 @-> ty1 @-> V_Set))
          >>= fun () ->
          has_type ctxt (apply (apply r1 a1) a2) prf
       | _ ->
          error_when_false false)

  | V_TmEq _, { term_loc } ->
     Error (Term_is_not_a_term_equality term_loc)

  | ( V_Zero | V_Succ _
    | V_Lam _ | V_Pair _ | V_QuotIntro _
    | V_Tag _
    | V_Irrel | V_Neutral _), _ ->
     failwith "internal error: has_type: attempting to check canonical term \
               against non canonical type"

and synthesise_head_type ctxt = function
  | { head_data = Bound _ } ->
     failwith "internal error: bound variable has got free"

  | { head_data = Free_local nm; head_loc } ->
     (match Context.lookup_local nm ctxt with
       | Ok ty ->
          Ok ty
       | Error (`VarNotFound nm) ->
          Error (VarNotFound (head_loc, nm)))

  | { head_data = Free_global nm; head_loc } ->
     (match Context.lookup_global nm ctxt with
       | Ok ty ->
          Ok ty
       | Error (`VarNotFound nm) ->
          Error (VarNotFound (head_loc, nm)))

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

  | { elims_data = App (elims, tm) } ->
     (synthesise_elims_type ctxt h elims >>= fun ty ->
      match expand_value ty with
        | V_Pi (s, VB (_, t)) ->
           has_type ctxt s tm >>= fun () ->
           Ok (t (Evaluation.eval0 ctxt tm))
        | ty ->
           let loc     = Syntax.location_of_neutral h elims in
           let arg_loc = Syntax.location_of_term tm in
           let ty      = reify_type ty 0 in
           Error (BadApplication {loc;arg_loc;ctxt;ty}))

  | { elims_data = ElimNat (elims, elim_ty, tm_z, tm_s); elims_loc } ->
     (synthesise_elims_type ctxt h elims >>= fun ty ->
      match expand_value ty with
        | V_Nat ->
           (let _, elim_ty, ctxt = ScopeClose.close V_Nat elim_ty ctxt in
            is_type ctxt elim_ty)
           >>= fun () ->
           let ty = Evaluation.eval1 ctxt elim_ty in
           has_type ctxt (ty V_Zero) tm_z >>= fun () ->
           (let n, _, tm_s, ctxt =
              ScopeClose.close2
                V_Nat
                (fun n -> ty n)
                tm_s
                ctxt
            in
            has_type ctxt (ty (V_Succ n)) tm_s) >>= fun () ->
           Ok (ty (Evaluation.eval0 ctxt (mk_term (Neutral (h, elims, None)))))
        | _ ->
           let ty     = reify_type_small ty 0 in
           let hd_loc = location_of_neutral h elims in
           let loc    = elims_loc in
           Error (BadNatElim { loc; hd_loc; ctxt; ty }))

  | { elims_data = ElimQ (elims, elim_ty, tm, tm_eq); elims_loc } ->
     (synthesise_elims_type ctxt h elims >>= fun ty ->
      match expand_value ty with
        | V_QuotType (ty_underlying, r) as ty ->
           (let _, elim_ty, ctxt = ScopeClose.close ty elim_ty ctxt in
            is_type ctxt elim_ty)
           >>= fun () ->
           let ty = Evaluation.eval1 ctxt elim_ty in
           (let n, tm, ctxt = ScopeClose.close ty_underlying tm ctxt in
            has_type ctxt (ty (V_QuotIntro n)) tm)
           >>= fun () ->
           let tm = Evaluation.eval1 ctxt tm in
           (let x1, x2, xr, tm_eq, ctxt =
              ScopeClose.close3
                ty_underlying
                (fun _ -> ty_underlying)
                (fun x1 x2 -> apply (apply r x1) x2)
                tm_eq
                ctxt
            in
            has_type ctxt (V_TmEq { s = tm x1; s_ty = ty (V_QuotIntro x1)
                                  ; t = tm x2; t_ty = ty (V_QuotIntro x2) }) tm_eq)
           >>= fun () ->
           Ok (ty (Evaluation.eval0 ctxt (mk_term (Neutral (h, elims, None)))))
        | _ ->
           let ty     = reify_type_small ty 0 in
           let hd_loc = location_of_neutral h elims in
           let loc    = elims_loc in
           Error (BadQuotElim { loc; hd_loc; ctxt; ty }))

  | { elims_data = Project (elims, `fst); elims_loc } ->
     (synthesise_elims_type ctxt h elims >>= fun ty ->
      match expand_value ty with
        | V_Sigma (s, t) ->
           Ok s
        | V_TyEq (V_Pi (s,t), V_Pi (s',t')) ->
           Ok (V_TyEq (s',s))
        | V_TyEq (V_Sigma (s,t), V_Sigma (s',t')) ->
           Ok (V_TyEq (s,s'))
        | ty ->
           let ty     = reify_type_small ty 0 in
           let hd_loc = location_of_neutral h elims in
           let loc    = elims_loc in
           Error (BadProject {loc;hd_loc;ctxt;ty}))

  | { elims_data = Project (elims, `snd); elims_loc } ->
     (synthesise_elims_type ctxt h elims >>= fun ty ->
      match expand_value ty with
        | V_Sigma (s, VB (_, t)) ->
           Ok (t (vfst (Evaluation.eval0 ctxt (mk_term (Neutral (h, elims, None))))))
        | V_TyEq (V_Pi (s, VB (x, t)), V_Pi (s', VB (x', t')))
        | V_TyEq (V_Sigma (s, VB (x, t)), V_Sigma (s', VB (x', t'))) ->
           Ok (V_Pi (s, VB (x, fun vs ->
               V_Pi (s', VB (x', fun vs' ->
                   V_Pi (V_TmEq { s=vs; s_ty=s; t=vs'; t_ty=s' },
                         VB (x^"_"^x', fun _ ->
                             V_TyEq (t vs, t' vs'))))))))
        | _ ->
           let ty     = reify_type_small ty 0 in
           let hd_loc = location_of_neutral h elims in
           let loc    = elims_loc in
           Error (BadProject {loc;hd_loc;ctxt;ty}))

  | { elims_data = ElimTag (elims, elim_ty, clauses); elims_loc } ->
     (synthesise_elims_type ctxt h elims >>= fun ty ->
      match expand_value ty with
        | V_TagType tags ->
           let unmatched =
             TagMap.fold
               (fun k _ -> TagSet.remove k)
               clauses
               tags
           and unmatchable =
             TagMap.fold
               (fun k _ s -> if TagSet.mem k tags then s else TagSet.add k s)
               clauses
               TagSet.empty
           in
           if TagSet.is_empty unmatched && TagSet.is_empty unmatchable then
             (let _, elim_ty, ctxt = ScopeClose.close ty elim_ty ctxt in
              is_type ctxt elim_ty)
             >>= fun () ->
             let ty = Evaluation.eval1 ctxt elim_ty in
             TagMap.fold
               (fun tag tm result ->
                  result >>= fun () ->
                  has_type ctxt (ty (V_Tag tag)) tm)
               clauses
               (Ok ())
             >>= fun () ->
             Ok (ty (Evaluation.eval0 ctxt (mk_term (Neutral (h, elims, None)))))
           else
             let hd_loc = location_of_neutral h elims in
             let loc    = elims_loc in
             Error (IncorrectTags { loc; hd_loc; unmatched; unmatchable })
        | _ ->
           let ty     = reify_type_small ty 0 in
           let hd_loc = location_of_neutral h elims in
           let loc    = elims_loc in
           Error (BadTagElim { loc; hd_loc; ctxt; ty }))

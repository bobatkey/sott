(* Hofmann's counterexample to just adding funext:

     assume two closed functions U, V : Bool -> Bool such that
        |- funext P : [U == V : Bool -> Bool]

     let F f = Bool

     then coerce(True,F U, F V, subst(Bool->Bool; x.F x; U; V; funext P)) : Bool

       but F U = F V = Bool, so this reduces to True -- no violation of canonicity.

   There is also a problem with inductive families with built-in equality:
      https://coq.inria.fr/cocorico/extensional_equality

   but this should be avoided by making equality explicit in inductive families
   (a la Epigram 2/Foveran)

   FIXME: the above is slightly wrong...
*)


type term =
  | Neutral of head * elims

  | Lam of term
  | Set
  | Pi of term * term
  | Sigma of term * term
  | Pair of term * term
  | Bool
  | True
  | False

  | TyEq of term * term
  | TmEq of { tm1 : term; ty1 : term; tm2 : term; ty2 : term }

  (* proof constructors *)
  | Subst of { ty_s : term
             ; ty_t : term
             ; tm_x : term
             ; tm_y : term
             ; tm_e : term
             }
  | Refl
  | Coh
  | Funext of term

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
  | App of elims * term
  | If  of elims * term * term * term
  | Project of elims * [`fst | `snd]

let bind x ?(offset=0) term =
  let rec bind_term x j = function
    | Neutral (head, elims) ->
       Neutral (bind_head x j head, bind_elims x j elims)
    | Lam t ->
       Lam (bind_term x (j+1) t)
    | Set ->
       Set
    | Pi (s, t) ->
       Pi (bind_term x j s, bind_term x (j+1) t)
    | Sigma (s, t) ->
       Sigma (bind_term x j s, bind_term x (j+1) t)
    | Pair (t1, t2) ->
       Pair (bind_term x j t1, bind_term x j t2)
    | TyEq (s, t) ->
       TyEq (bind_term x j s, bind_term x j t)
    | TmEq {tm1;ty1;tm2;ty2} ->
       TmEq { tm1 = bind_term x j tm1
            ; ty1 = bind_term x j ty1
            ; tm2 = bind_term x j tm2
            ; ty2 = bind_term x j ty2
            }
    | (Bool | True | False) as t -> t
    | Subst { ty_s; ty_t; tm_x; tm_y; tm_e } ->
       Subst { ty_s = bind_term x j ty_s
             ; ty_t = bind_term x (j+1) ty_t
             ; tm_x = bind_term x j tm_x
             ; tm_y = bind_term x j tm_y
             ; tm_e = bind_term x j tm_e
             }
    | (Refl | Coh) as t -> t
    | Funext e ->
       Funext (bind_term x (j+3) e)
    | Irrel ->
       failwith "internal error: attempt to bind in an erased proof term"

  and bind_head x j = function
    | Bound _ as h -> h
    | Free nm as h -> if nm = x then Bound j else h
    | Coerce { coercee; src_type; tgt_type; eq_proof } ->
       Coerce { coercee  = bind_term x j coercee
              ; src_type = bind_term x j src_type
              ; tgt_type = bind_term x j tgt_type
              ; eq_proof = bind_term x j eq_proof
              }

  and bind_elims x j = function
    | Nil ->
       Nil
    | App (elims, tm) ->
       App (bind_elims x j elims, bind_term x j tm)
    | If (elims, ty, tm_t, tm_f) ->
       If (bind_elims x j elims,
           bind_term x (j+1) ty,
           bind_term x j tm_t,
           bind_term x j tm_f)
    | Project (elims, component) ->
       Project (bind_elims x j elims, component)
  in
  bind_term x offset term

let rec close x j = function
  | Neutral (h, elims) ->
     Neutral (close_head x j h, close_elims x j elims)
  | Lam t -> Lam (close x (j+1) t)
  | Set -> Set
  | Pi (s, t) -> Pi (close x j s, close x (j+1) t)
  | Sigma (s, t) -> Sigma (close x j s, close x (j+1) t)
  | Pair (s, t) -> Pair (close x j s, close x j t)
  | TyEq (s, t) -> TyEq (close x j s, close x j t)
  | TmEq {tm1;ty1;tm2;ty2} ->
     TmEq { tm1 = close x j tm1
          ; ty1 = close x j ty1
          ; tm2 = close x j tm2
          ; ty2 = close x j ty2
          }
  | (Bool | True | False) as t -> t
  | Subst s ->
     Subst { ty_s = close x j s.ty_s
           ; ty_t = close x (j+1) s.ty_t
           ; tm_x = close x j s.tm_x
           ; tm_y = close x j s.tm_y
           ; tm_e = close x j s.tm_e
           }
  | Refl ->
     Refl
  | Coh ->
     Coh
  | Funext e ->
     Funext (close x (j+3) e)
  | Irrel ->
     Irrel

and close_head x j = function
  | Bound i ->
     if i = j then Free x else Bound i
  | Free nm ->
     Free nm
  | Coerce { coercee; src_type; tgt_type; eq_proof } ->
     Coerce { coercee  = close x j coercee
            ; src_type = close x j src_type
            ; tgt_type = close x j tgt_type
            ; eq_proof = close x j eq_proof
            }

and close_elims x j = function
  | Nil ->
     Nil
  | App (elims, tm) ->
     App (close_elims x j elims, close x j tm)
  | If (elims, ty, tm_t, tm_f) ->
     If (close_elims x j elims,
         close x (j+1) ty,
         close x j tm_t,
         close x j tm_f)
  | Project (elims, component) ->
     Project (close_elims x j elims, component)

(******************************************************************************)
type shift = int

type value =
  | V_Neu     of v_head * v_elims
  | V_Lam     of (value -> value)
  | V_Set
  | V_Bool
  | V_True
  | V_False
  | V_Pi      of value * (value -> value)
  | V_Sigma   of value * (value -> value)
  | V_Pair    of value * value
  | V_TyEq    of value * value
  | V_TmEq    of { s : value; s_ty : value; t : value; t_ty : value }
  | V_Irrel

and v_elims =
  | E_Nil
  | E_App of v_elims * value
  | E_If  of v_elims * (value -> value) * value * value
  | E_Project of v_elims * [`fst|`snd]

and v_head =
  | H_Var     of { shift : shift; typ : value }
  | H_Free    of { name  : string; typ : value }
  | H_Coe     of { coercee  : value
                 ; src_type : value
                 ; tgt_type : value
                 }

let apply v1 v2 = match v1 with
  | V_Lam f       -> f v2
  | V_Neu (h, es) -> V_Neu (h, E_App (es, v2))
  | _             -> failwith "internal type error"

let rec eval_elims t = function
  | E_Nil -> t
  | E_App (es, v) -> apply (eval_elims t es) v
  | E_If (es, ty, v_t, v_f) ->
     (match eval_elims t es with
       | V_True        -> v_t
       | V_False       -> v_f
       | V_Neu (h, es) -> V_Neu (h, E_If (es, ty, v_t, v_f))
       | _ -> failwith "type error")
  | E_Project (es, component) ->
     (match eval_elims t es, component with
       | V_Pair (v, _), `fst -> v
       | V_Pair (_, v), `snd -> v
       | V_Neu (h, es), _    -> V_Neu (h, E_Project (es, component))
       | _  -> failwith "internal error: type error in projection")
       

let var ty i =
  V_Neu (H_Var { shift = i; typ = ty }, E_Nil)

let free x ty =
  V_Neu (H_Free { name = x; typ = ty }, E_Nil)

let vfst = function
  | V_Pair (v, _) -> v
  | V_Neu (h, es) -> V_Neu (h, E_Project (es, `fst))
  | _             -> failwith "internal error: type error in vfst"

let vsnd = function
  | V_Pair (_, v) -> v
  | V_Neu (h, es) -> V_Neu (h, E_Project (es, `snd))
  | _             -> failwith "internal error: type error in vsnd"

(**********************************************************************)
(* FIXME: equality test rather than reify to term and check for equal?
   *)

let rec reify_type v i = match v with
  | V_Pi (s, t) ->
     Pi (reify_type s i, reify_type (t (var s i)) (i+1))
  | V_Sigma (s, t) ->
     Sigma (reify_type s i, reify_type (t (var s i)) (i+1))
  | V_Set         -> Set
  | V_Bool        -> Bool
  | V_TyEq (s, t) -> TyEq (reify_type s i, reify_type t i)
  | V_TmEq {s; s_ty; t; t_ty} ->
     TmEq { tm1 = reify s_ty s i
          ; ty1 = reify_type s_ty i
          ; tm2 = reify t_ty t i
          ; ty2 = reify_type t_ty i
          }
  | V_Neu (h, es) -> reify_neutral h es i
  | _             -> failwith "Blah"

and reify ty v i = match ty, v with
  | V_Pi (s, t), f -> let v = var s i in Lam (reify (t v) (apply f v) (i+1))
  | V_Sigma (s, t), p ->
     Pair (reify s (vfst p) i, reify (t (vfst p)) (vsnd p) i)
  | V_TyEq _, v       -> Irrel
  | V_TmEq _, v       -> Irrel
  | V_Bool,   V_True  -> True
  | V_Bool,   V_False -> False
  | V_Set,    v       -> reify_type v i
  | _,        V_Neu (h, es) -> reify_neutral h es i
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
     if ty1_tm = ty2_tm then
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
       | es, V_Pi (s, t) ->
          App (es, reify s v i), t v
       | _ ->
          failwith "internal error: type error reifying application")
  | E_If (es, elim_ty, v_t, v_f) ->
     (match reify_elims h ty es i with
       | es', V_Bool ->
          If (es',
              reify_type (elim_ty (var V_Bool i)) (i+1),
              reify (elim_ty V_True) v_t i,
              reify (elim_ty V_False) v_f i),
          elim_ty (V_Neu (h, es))
       | _ ->
          failwith "internal error: type error reifying bool case switch")
  | E_Project (es, component) ->
     (match reify_elims h ty es i, component with
       | (reified_es, V_Sigma (s, t)), `fst ->
          Project (reified_es, `fst), s
       | (reified_es, V_Sigma (s, t)), `snd ->
          Project (reified_es, `snd), t (V_Neu (h, es))
       | _ ->
          failwith "internal error: type error reifying a projection")

let equal_types ty1 ty2 =
  let ty1 = reify_type ty1 0 in
  let ty2 = reify_type ty2 0 in
  ty1 = ty2

let equal_terms tm1 tm2 ty =
  let tm1 = reify ty tm1 0 in
  let tm2 = reify ty tm2 0 in
  tm1 = tm2

(**********************************************************************)
(* Contexts *)

module Context : sig
  type t

  val empty : t
  val extend : t -> value -> string * t
  val lookup : string -> t -> (value, [>`Msg of string]) result
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
         Error (`Msg (Printf.sprintf "variable '%s' not found" nm))
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
let rec coerce v src tgt = match v, src, tgt with
  | v, V_Bool, V_Bool -> v
  | v, V_Set,  V_Set  -> v
  | f, V_Pi (ty_s,ty_t), V_Pi (ty_s',ty_t') ->
     V_Lam
       (fun s' ->
          let s = coerce s' ty_s' ty_s in
          let t = apply f s in
          coerce t (ty_t' s') (ty_t s))
  | p, V_Sigma (ty_s,ty_t), V_Sigma (ty_s', ty_t') ->
     let s' = coerce (vfst p) ty_s ty_s' in
     V_Pair (s', coerce (vsnd p) (ty_t (vfst p)) (ty_t' s'))
  | _, V_TyEq _, V_TyEq _ (* FIXME: these two cases could go straight to irrel? *)
  | _, V_TmEq _, V_TmEq _
  | _, V_Neu _, _
  | _, _, V_Neu _ ->
     V_Neu (H_Coe { coercee = v; src_type = src; tgt_type = tgt }, E_Nil)
  | _ ->
     (* FIXME: ought to be a suspended falsity elimination *)
     V_Neu (H_Coe { coercee = v; src_type = src; tgt_type = tgt }, E_Nil)

let evaluate ctxt tm =
  let rec eval tm env = match tm with
    | Neutral (h, es) -> eval_elims (eval_head h env) es env
    | Lam t           -> V_Lam (fun v -> eval t (v::env))
    | Set             -> V_Set
    | Pi (t1, t2)     -> V_Pi (eval t1 env, fun v -> eval t2 (v::env))
    | Sigma (s, t)    -> V_Sigma (eval s env, fun v -> eval t (v::env))
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
            V_Neu (H_Free { name = nm; typ }, E_Nil)
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
         | V_Neu (h, es) ->
            V_Neu (h, E_If (es, (fun v -> eval ty (v::env)),
                            eval tm_t env, eval tm_f env))
         | _ -> failwith "internal type error: eval_elims If")
    | Project (elims, `fst) ->
       vfst (eval_elims scrutinee elims env)
    | Project (elims, `snd) ->
       vsnd (eval_elims scrutinee elims env)
  in
  eval tm

let eval_closed ctxt tm = evaluate ctxt tm []

(******************************************************************************)
(* Now a type checker:
   - bidirectional type checker
   - use NbE above to check types for equality (misses out eta for funcs, for now)
   - coercion switches the direction: checks its internal thing, synthesises its external.

   - checking that [S = T] is a type: S and T are types
   - checking that [s : S = t : T] is a type: S and T are types, and s, t are checked to be members of them
   - synthesising a type for coe(S,T,e,s) : check that S and T are types, check s : S and e : [S=T], return T
   - all equality proof rules synthesise their type?
*)

let rec is_type ctxt = function
  | Set -> Ok ()
  | Bool -> Ok ()
  | Pi (s, t) ->
     (match is_type ctxt s with
       | Ok () ->
          let x, ctxt = Context.extend ctxt (eval_closed ctxt s) in
          is_type ctxt (close x 0 t)
       | Error msg ->
          Error msg)
  | Sigma (s, t) ->
     (match is_type ctxt s with
       | Ok () ->
          let x, ctxt = Context.extend ctxt (eval_closed ctxt s) in
          is_type ctxt (close x 0 t)
       | Error msg ->
          Error msg)
  | TyEq (s, t) ->
     (match is_type ctxt s with
       | Ok ()     -> is_type ctxt t
       | Error msg -> Error msg)
  | TmEq {tm1; ty1; tm2; ty2} ->
     (match is_type ctxt ty1, is_type ctxt ty2 with
       | Ok (), Ok () ->
          let ty1 = eval_closed ctxt ty1 in
          let ty2 = eval_closed ctxt ty2 in
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
  | V_Pi (s, t), Lam tm ->
     let x, ctxt = Context.extend ctxt s in
     has_type ctxt (t (free x s)) (close x 0 tm)
  | V_Sigma (s, t), Pair (tm_s, tm_t) ->
     (match has_type ctxt s tm_s with
       | Ok () ->
          let tm_s = eval_closed ctxt tm_s in
          has_type ctxt (t tm_s) tm_t
       | Error msg ->
          Error msg)
  | V_Set, Bool ->
     Ok ()
  | V_Set, Pi (s, t) ->
     (match has_type ctxt V_Set s with
       | Ok () ->
          let x, ctxt = Context.extend ctxt (eval_closed ctxt s) in
          has_type ctxt V_Set (close x 0 t)
       | Error msg ->
          Error msg)
  | V_Set, Sigma (s, t) ->
     (match has_type ctxt V_Set s with
       | Ok () ->
          let x, ctxt = Context.extend ctxt (eval_closed ctxt s) in
          has_type ctxt V_Set (close x 0 t)
       | Error msg ->
          Error msg)
  | V_Set, TyEq (s, t) ->
     (match is_type ctxt s with
       | Ok ()     -> is_type ctxt t
       | Error msg -> Error msg)
  | V_Set, TmEq {tm1; ty1; tm2; ty2} ->
     (match is_type ctxt ty1, is_type ctxt ty2 with
       | Ok (), Ok () ->
          let ty1 = eval_closed ctxt ty1 in
          let ty2 = eval_closed ctxt ty2 in
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
          (let ty_s = eval_closed ctxt ty_s in
           match
             let x, ctxt = Context.extend ctxt ty_s in
             is_type ctxt (close x 0 ty_t)
           with
             | Ok () ->
                (let ty_t v = evaluate ctxt ty_t [v] in
                 match has_type ctxt ty_s tm_x, has_type ctxt ty_s tm_y with
                   | Ok (), Ok () ->
                      (let tm_x = eval_closed ctxt tm_x in
                       let tm_y = eval_closed ctxt tm_y in
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

  | V_TmEq {s=tm_f1; s_ty=V_Pi (s1, t1); t=tm_f2; t_ty=V_Pi (s2, t2)},
    Funext proof ->
     let x1, ctxt = Context.extend ctxt s1 in
     let x1v      = free x1 s1 in
     let x2, ctxt = Context.extend ctxt s2 in
     let x2v      = free x2 s2 in
     let xe, ctxt =
       Context.extend ctxt (V_TmEq {s=x1v; s_ty=s2; t=x2v; t_ty=s2}) in
     let proof    = close xe 0 (close x2 1 (close x1 2 proof)) in
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
       V_Neu (H_Coe { coercee = s; src_type = s_ty; tgt_type = t_ty }, E_Nil)
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
          if ty = ty'
          then Ok ()
          else Error (`Type_mismatch (ty, ty'))
       | Error msg -> Error msg)

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
          let ty1 = eval_closed ctxt src_type in
          let ty2 = eval_closed ctxt tgt_type in
          (match has_type ctxt ty1 coercee,
                 has_type ctxt (V_TyEq (ty1, ty2)) eq_proof with
            | Ok (), Ok () ->
               Ok ty2
            | _ ->
               Error (`Msg "failed to type check a coercion"))
       | Error msg, _ ->
          Error msg
       | Ok (), Error msg ->
          Error msg

and synthesise_elims_type ctxt h = function
  | Nil ->
     synthesise_head_type ctxt h
  | App (elims, tm) ->
     (match synthesise_elims_type ctxt h elims with
       | Ok (V_Pi (s, t)) ->
          (match has_type ctxt s tm with
            | Ok ()   -> Ok (t (eval_closed ctxt tm))
            | Error e -> Error e)
       | Ok _    ->
          Error (`Msg "attempt to apply non function")
       | Error e -> Error e)
  | If (elims, elim_ty, tm_t, tm_f) ->
     (match synthesise_elims_type ctxt h elims with
       | Ok V_Bool ->
          (match
             let x, ctxt = Context.extend ctxt V_Bool in
             is_type ctxt (close x 0 elim_ty)
           with
             | Ok () ->
                let ty v = evaluate ctxt elim_ty [v] in
                (match (has_type ctxt (ty V_True) tm_t,
                        has_type ctxt (ty V_False) tm_f) with
                  | Ok (), Ok () ->
                     Ok (ty (eval_closed ctxt (Neutral (h, elims))))
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
       | Ok (V_Sigma (s, t)) ->
          Ok (t (eval_closed ctxt (Neutral (h, elims))))
       | Ok (V_TyEq (V_Pi (s,t), V_Pi (s',t')))
       | Ok (V_TyEq (V_Sigma (s,t), V_Sigma (s',t'))) ->
          Ok (V_Pi (s, fun vs ->
              V_Pi (s', fun vs' ->
                  V_Pi (V_TmEq { s=vs; s_ty=s; t=vs'; t_ty=s' }, fun _ ->
                      V_TyEq (t vs, t' vs')))))
       | Ok _ ->
          Error (`Msg "attempt to project from expression of non pair type")
       | Error msg ->
          Error msg)

(*
   subst : (A : Set) -> (B : A -> Set) -> (a : A) -> B a -> (a' : A) -> [a : A = a' : A] -> B a'
   subst A B a b a' e = coerce  

   Need pairs? and then prove that [(a,refl)=(b,e)] (how? an axiom?)

   J(A; a; x:A,e:[a:A=x:A].C; H; b; e) : C[b,e] :=
      coerce(   , C[a,refl], C[b,e], subst(

   J(A; x:A,y:A,e:[x:A=y:A].C; x:A.H; a; b; e) : C[a,b,e] :=
      coerce(H[a], C[a,a,refl], C[a,b,e], 

subst(A; x:A.(e : [a:A=x:A]) -> C[a,x,e]; a; b; e) : [(e : [a:A=a:A]) -> 

    H(a) : C(a,b,

*)

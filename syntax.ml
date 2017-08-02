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
*)


type term =
  | Neutral of head * elims

  | Lam of term
  | Set
  | Pi  of term * term
  | Bool
  | True
  | False

  | TyEq of term * term
  | TmEq of term * term * term * term

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
    | TyEq (s, t) ->
       TyEq (bind_term x j s, bind_term x j t)
    | TmEq (s, ty_s, t, ty_t) ->
       TmEq (bind_term x j s, bind_term x j ty_s,
             bind_term x j t, bind_term x j ty_t)
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
  in
  bind_term x offset term

let rec close x j = function
  | Neutral (h, elims) ->
     Neutral (close_head x j h, close_elims x j elims)
  | Lam t -> Lam (close x (j+1) t)
  | Set -> Set
  | Pi (s, t) -> Pi (close x j s, close x (j+1) t)
  | TyEq (s, t) -> TyEq (close x j s, close x j t)
  | TmEq (s, ty_s, t, ty_t) ->
     TmEq (close x j s, close x j ty_s, close x j t, close x j ty_t)
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
  | V_TyEq    of value * value
  | V_TmEq    of value * value * value * value
  | V_Irrel

and v_elims =
  | E_Nil
  | E_App of v_elims * value
  | E_If  of v_elims * (value -> value) * value * value

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
     match eval_elims t es with
       | V_True        -> v_t
       | V_False       -> v_f
       | V_Neu (h, es) -> V_Neu (h, E_If (es, ty, v_t, v_f))
       | _ -> failwith "type error"

let var ty i =
  V_Neu (H_Var { shift = i; typ = ty }, E_Nil)

let free x ty =
  V_Neu (H_Free { name = x; typ = ty }, E_Nil)

(**********************************************************************)
(* FIXME: equality test rather than reify to term and check for equal?
   *)

let rec reify_type v i = match v with
  | V_Pi (s, t)   -> Pi (reify_type s i, reify_type (t (var s i)) (i+1))
  | V_Set         -> Set
  | V_Bool        -> Bool
  | V_TyEq (s, t) -> TyEq (reify_type s i, reify_type t i)
  | V_TmEq (s, s_ty, t, t_ty) ->
     TmEq (reify s_ty s i, reify_type s_ty i,
           reify t_ty t i, reify_type t_ty i)
  | V_Neu (h, es) -> reify_neutral h es i
  | _             -> failwith "Blah"

and reify ty v i = match ty, v with
  | V_Pi (s, t), f -> let v = var s i in Lam (reify (t v) (apply f v) (i+1))
  | V_TyEq _, v       -> Irrel
  | V_TmEq _, v       -> Irrel
  | V_Bool,   V_True  -> True
  | V_Bool,   V_False -> False
  | V_Set,    v       -> reify_type v i
  | _,        V_Neu (h, es) -> reify_neutral h es i
  | _                 -> failwith "internal error: reification failed"

and reify_neutral h es i = match h with
  | H_Var { shift; typ } ->
     Neutral (Bound (i-shift-1), reify_elims typ es i)
  | H_Free { name; typ } ->
     Neutral (Free name, reify_elims typ es i)
  | H_Coe { coercee; src_type; tgt_type } ->
     let ty1_tm = reify_type src_type i in
     let ty2_tm = reify_type tgt_type i in
     if ty1_tm = ty2_tm then
       reify src_type (eval_elims coercee es) i
     else
       let h =
         Coerce { coercee  = reify src_type coercee i
                ; src_type = ty1_tm
                ; tgt_type = ty2_tm
                ; eq_proof = Irrel
                }
       in
       Neutral (h, reify_elims tgt_type es i)

and reify_elims ty es i = match ty, es with
  | _, E_Nil ->
     Nil
  | V_Pi (s, t), E_App (es, v) ->
     App (reify_elims (t v) es i, reify s v i)
  | _, E_App _ ->
     failwith "internal error: type error reifying application"
  | _, E_If (es, ty, v_t, v_f) ->
     If (reify_elims V_Bool es i,
         reify_type (ty (var V_Bool i)) (i+1),
         reify (ty V_True) v_t i,
         reify (ty V_False) v_f i)

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
let evaluate ctxt tm =
  let rec eval tm env = match tm with
    | Neutral (h, es) -> eval_elims (eval_head h env) es env
    | Lam t           -> V_Lam (fun v -> eval t (v::env))
    | Set             -> V_Set
    | Pi (t1, t2)     -> V_Pi (eval t1 env, fun v -> eval t2 (v::env))
    | TyEq (s, t)     -> V_TyEq (eval s env, eval t env)
    | TmEq (s, s_ty, t, t_ty) ->
       V_TmEq (eval s env, eval s_ty env, eval t env, eval t_ty env)
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
       V_Neu (H_Coe { coercee  = eval coercee env
                    ; src_type = eval src_type env
                    ; tgt_type = eval tgt_type env
                    }, E_Nil)
  and eval_elims scrutinee elims env = match elims with
    | Nil ->
       scrutinee
    | App (elims, tm) ->
       apply (eval_elims scrutinee elims env) (eval tm env)
    | If (elims, ty, tm_t, tm_f) ->
       match eval_elims scrutinee elims env with
         | V_True  -> eval tm_t env
         | V_False -> eval tm_f env
         | V_Neu (h, es) ->
            V_Neu (h, E_If (es, (fun v -> eval ty (v::env)),
                            eval tm_t env, eval tm_f env))
         | _ -> failwith "internal type error: eval_elims If"
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
  | TyEq (s, t) ->
     (match is_type ctxt s with
       | Ok ()     -> is_type ctxt t
       | Error msg -> Error msg)
  | TmEq (s, s_ty, t, t_ty) ->
     (match is_type ctxt s_ty, is_type ctxt t_ty with
       | Ok (), Ok () ->
          let s_ty = eval_closed ctxt s_ty in
          let t_ty = eval_closed ctxt t_ty in
          (match has_type ctxt s_ty s, has_type ctxt t_ty t with
            | Ok (), Ok () ->
               Ok ()
            | _ ->
               Error (`Msg "term(s) not of right type in term equality"))
       | Error msg, _ ->
          Error msg
       | Ok _, Error msg ->
          Error msg)
  (* FIXME: only remaining possibility is Neutral: synthesise the type
     and check that it is Set for some set level. *)
  | tm ->
     has_type ctxt V_Set tm

and has_type ctxt ty tm = match ty, tm with
  | V_Pi (s, t), Lam tm ->
     let x, ctxt = Context.extend ctxt s in
     has_type ctxt (t (free x s)) (close x 0 tm)
  | V_Set, Bool ->
     Ok ()
  | V_Set, Pi (s, t) ->
     (match has_type ctxt V_Set s with
       | Ok () ->
          let x, ctxt = Context.extend ctxt (eval_closed ctxt s) in
          has_type ctxt V_Set (close x 0 t)
       | Error msg ->
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
                      let tm_x = eval_closed ctxt tm_x in
                      let tm_y = eval_closed ctxt tm_y in
                      (match
                         has_type ctxt (V_TmEq (tm_x, ty_s, tm_y, ty_s)) tm_e
                       with
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

  | V_TmEq (tm1, ty1, tm2, ty2), Refl ->
     if equal_types ty1 ty2 then
       (if equal_terms tm1 tm2 ty1 then
          Ok ()
        else
          Error (`Msg "terms not equal in refl"))
     else
       Error (`Msg "types not equal in refl")

  | V_TmEq (tm_f1, V_Pi (s1, t1), tm_f2, V_Pi (s2, t2)), Funext proof ->
     let x1, ctxt = Context.extend ctxt s1 in
     let x1v      = free x1 s1 in
     let x2, ctxt = Context.extend ctxt s2 in
     let x2v      = free x2 s2 in
     let xe, ctxt = Context.extend ctxt (V_TmEq (x1v, s2, x2v, s2)) in
     let proof    = close xe 0 (close x2 1 (close x1 2 proof)) in
     let reqd_ty  =
       V_TmEq (apply tm_f1 x1v, t1 x1v,
               apply tm_f2 x2v, t2 x2v)
     in
     has_type ctxt reqd_ty proof

  | V_TmEq (tm_a, ty_a, tm_b, ty_b), Coh ->
     let tm_b' =
       V_Neu (H_Coe { coercee = tm_a; src_type = ty_a; tgt_type = ty_b }, E_Nil)
     in
     if equal_terms tm_b tm_b' ty_b then
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

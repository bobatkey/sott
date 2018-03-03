module Tag = struct
  type t = string
  let compare = String.compare
  let equal = String.equal
end
module TagMap = struct
  include Map.Make (Tag)
  let of_bindings bs =
    List.fold_right (fun (tag,v) -> add tag v) bs empty
end
module TagSet = Set.Make (Tag)

type tag = Tag.t
type tag_set = TagSet.t
type 'a tag_map = 'a TagMap.t

type 'a binder = B of string * 'a

type level = int

type term =
  { term_loc  : Location.t
  ; term_data : term_data
  }

and term_data =
  | Neutral of head * elims * term Lazy.t option

  | Set of level

  | Pi of term * term binder
  | Lam of term binder

  | QuotType  of term * term
  | QuotIntro of term

  | Sigma of term * term binder
  | Pair of term * term

  | Nat
  | Zero
  | Succ of term

  | TagType of tag_set
  | Tag of tag

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
  | Coh of term
  | Funext of term binder binder binder
  | SameClass of term

  (* placeholder for an erased proof term; only generated during
     reification. *)
  | Irrel

and head =
  { head_loc  : Location.t
  ; head_data : head_data
  }

and head_data =
  | Bound  of int
  | Free_local of string
  | Free_global of string
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
  | App      of elims * term
  | Project  of elims * [`fst | `snd]
  | ElimNat  of elims * term binder * term * term binder binder
  | ElimQ    of elims * term binder * term binder * term binder binder binder
  | ElimTag  of elims * term binder * term tag_map

let mk_elim elims_data =
  { elims_data; elims_loc = Location.generated }
let mk_term term_data =
  { term_data; term_loc = Location.generated }
let mk_head head_data =
  { head_data; head_loc = Location.generated }

let location_of_term term =
  term.term_loc

let location_of_neutral h elims =
  Location.mk_span h.head_loc elims.elims_loc


module AlphaEquality = struct

  let binder k (B (_, t1)) (B (_, t2)) =
    k t1 t2

  let rec equal_term t1 t2 = match t1.term_data, t2.term_data with
    | Neutral (h1, es1, reduced_opt1), Neutral (h2, es2, reduced_opt2) ->
       (equal_head h1 h2 && equal_elims es1 es2)
       || (match reduced_opt1, reduced_opt2 with
           | None,           None           -> false
           | Some (lazy t1), None           -> equal_term t1 t2
           | None,           Some (lazy t2) -> equal_term t1 t2
           | Some (lazy t1), Some (lazy t2) -> equal_term t1 t2)
    | Neutral (_, _, Some (lazy t1)), _ ->
       equal_term t1 t2
    | _, Neutral (_, _, Some (lazy t2)) ->
       equal_term t1 t2
    | Lam t1, Lam t2 ->
       binder equal_term t1 t2
    | Set i, Set j ->
       i = j
    | Pi (s1, t1), Pi (s2, t2)
    | Sigma (s1, t1), Sigma (s2, t2) ->
       equal_term s1 s2 && binder equal_term t1 t2
    | Pair (s1, t1), Pair (s2, t2) ->
       equal_term s1 s2 && equal_term t1 t2

    | QuotType (t1, r1), QuotType (t2, r2) ->
       equal_term t1 t2 && equal_term r1 r2
    | QuotIntro t1, QuotIntro t2 ->
       equal_term t1 t2

    | Nat, Nat
    | Zero, Zero ->
       true
    | Succ t1, Succ t2 ->
       equal_term t1 t2
    | TagType tags1, TagType tags2 ->
       TagSet.equal tags1 tags2
    | Tag tag1, Tag tag2 ->
       Tag.equal tag1 tag2
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
    | Refl, Refl ->
       true
    | Funext e, Funext e' ->
       binder (binder (binder equal_term)) e e'
    | SameClass e, SameClass e'
    | Coh e, Coh e' ->
       equal_term e e'
    | Irrel, Irrel ->
       true
    | _, _ ->
       false

  and equal_head h1 h2 = match h1.head_data, h2.head_data with
    | Bound i, Bound j -> i = j
    | Free_local nm, Free_local nm' -> nm = nm'
    | Free_global nm, Free_global nm' -> nm = nm'
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
    | ElimNat (es,  ty,  tm_z,  tm_s),
      ElimNat (es', ty', tm_z', tm_s') ->
       equal_elims es es' &&
       binder equal_term ty ty' &&
       equal_term tm_z tm_z' &&
       binder (binder equal_term) tm_s tm_s'
    | ElimQ (es,  ty,  tm,  tm_eq),
      ElimQ (es', ty', tm', tm_eq') ->
       equal_elims es es' &&
       binder equal_term ty ty' &&
       binder equal_term tm tm' &&
       binder (binder (binder equal_term)) tm_eq tm_eq'
    | ElimTag (es, ty, clauses),
      ElimTag (es', ty', clauses') ->
       equal_elims es es' &&
       binder equal_term ty ty' &&
       TagMap.equal equal_term clauses clauses'
    | Project (es, dir), Project (es', dir') ->
       dir = dir' && equal_elims es es'
    | _, _ ->
       false

end

let alpha_eq = AlphaEquality.equal_term

(**********************************************************************)
module type EXTENDABLE_CONTEXT = sig
  type t

  type ty

  type tm

  val extend : string -> ty -> t -> string * t

  val mk_free : string -> ty -> tm
end

module Scoping : sig
  val bind : string option -> term -> term binder

  val bind2 : string option -> string option -> term -> term binder binder

  val bind3 : string option -> string option -> string option -> term -> term binder binder binder

  module Close (Ctxt : EXTENDABLE_CONTEXT) : sig
    val close :
      Ctxt.ty ->
      term binder ->
      Ctxt.t ->
      Ctxt.tm * term * Ctxt.t

    val close2 :
      Ctxt.ty ->
      (Ctxt.tm -> Ctxt.ty) ->
      term binder binder ->
      Ctxt.t ->
      Ctxt.tm * Ctxt.tm * term * Ctxt.t

    val close3 :
      Ctxt.ty ->
      (Ctxt.tm -> Ctxt.ty) ->
      (Ctxt.tm -> Ctxt.tm -> Ctxt.ty) ->
      term binder binder binder ->
      Ctxt.t ->
      Ctxt.tm * Ctxt.tm * Ctxt.tm * term * Ctxt.t
  end
end = struct
  let binder k j = function
    | B (nm, t) -> B (nm, k (j+1) t)

  let traverse ~free ~bound j tm =
    let rec traverse_term j tm =
      match tm.term_data with
        | Neutral (head, elims, reduced_opt) ->
           { tm with
               term_data =
                 Neutral (traverse_head j head,
                          traverse_elims j elims,
                          match reduced_opt with
                            | None -> None
                            | Some reduced ->
                               Some (lazy (traverse_term j (Lazy.force reduced)))) }
        | Lam t ->
           { tm with term_data = Lam (binder traverse_term j t) }
        | Pi (s, t) ->
           { tm with term_data = Pi (traverse_term j s, binder traverse_term j t) }
        | Sigma (s, t) ->
           { tm with term_data = Sigma (traverse_term j s, binder traverse_term j t) }
        | Pair (t1, t2) ->
           { tm with term_data = Pair (traverse_term j t1, traverse_term j t2) }
        | QuotType (s, r) ->
           { tm with term_data = QuotType (traverse_term j s, traverse_term j r) }
        | QuotIntro t ->
           { tm with term_data = QuotIntro (traverse_term j t) }
        | TyEq (s, t) ->
           { tm with term_data = TyEq (traverse_term j s, traverse_term j t) }
        | TmEq {tm1;ty1;tm2;ty2} ->
           { tm with
               term_data = TmEq { tm1 = traverse_term j tm1
                                ; ty1 = traverse_term j ty1
                                ; tm2 = traverse_term j tm2
                                ; ty2 = traverse_term j ty2
                                } }
        | Nat | Zero | Refl | Set _ | TagType _ | Tag _ ->
           tm
        | Succ t ->
           { tm with term_data = Succ (traverse_term j t) }
        | Subst { ty_s; ty_t; tm_x; tm_y; tm_e } ->
           { tm with
               term_data = Subst { ty_s = traverse_term j ty_s
                                 ; ty_t = binder traverse_term j ty_t
                                 ; tm_x = traverse_term j tm_x
                                 ; tm_y = traverse_term j tm_y
                                 ; tm_e = traverse_term j tm_e
                                 } }
        | Funext prf ->
           { tm with term_data = Funext (binder (binder (binder traverse_term)) j prf) }
        | SameClass prf ->
           { tm with term_data = SameClass (traverse_term j prf) }
        | Coh prf ->
           { tm with term_data = Coh (traverse_term j prf) }
        | Irrel ->
           tm

    and traverse_head j h =
      match h.head_data with
        |  Bound i  ->
           { h with head_data = bound i j }
        |  Free_global nm  ->
           { h with head_data = free nm j }
        |  Free_local _  ->
           h
        |  Coerce { coercee; src_type; tgt_type; eq_proof  } ->
           { h with
               head_data =
                 Coerce { coercee  = traverse_term j coercee
                        ; src_type = traverse_term j src_type
                        ; tgt_type = traverse_term j tgt_type
                        ; eq_proof = traverse_term j eq_proof
                        } }

    and traverse_elims j es =
      match es.elims_data with
        | Nil  ->
           { es with elims_data = Nil }
        | App (elims, tm)  ->
           { es with
               elims_data = App (traverse_elims j elims, traverse_term j tm) }
        | Project (elims, component)  ->
           { es with
               elims_data = Project (traverse_elims j elims, component) }
        | ElimNat (elims, ty, tm_z, tm_s)  ->
           { es with
               elims_data = ElimNat (traverse_elims j elims,
                                     binder traverse_term j ty,
                                     traverse_term j tm_z,
                                     binder (binder traverse_term) j tm_s) }
        | ElimQ (elims, ty, tm, tm_eq)  ->
           { es with
               elims_data = ElimQ (traverse_elims j elims,
                                   binder traverse_term j ty,
                                   binder traverse_term j tm,
                                   binder (binder (binder traverse_term)) j tm_eq)
           }
        | ElimTag (elims, ty, clauses)  ->
           { es with elims_data = ElimTag (traverse_elims j elims,
                                           binder traverse_term j ty,
                                           TagMap.map (traverse_term j) clauses) }
    in
    traverse_term j tm

  let close_term x =
    traverse
      ~free:(fun nm _j -> Free_global nm)
      ~bound:(fun i j -> if i = j then Free_local x else Bound i)

  let bind_term = function
    | None -> fun _ t -> t
    | Some x ->
       traverse
         ~free:(fun nm j -> if nm = x then Bound j else Free_global nm)
         ~bound:(fun i _j -> Bound i)

  let ident_of_binder = function
    | None -> "x"
    | Some x -> x

  let bind x t =
    B (ident_of_binder x, bind_term x 0 t)

  let bind2 x y t =
    let t1 = B (ident_of_binder y, bind_term y 0 t) in
    let t2 = B (ident_of_binder x, binder (bind_term x) 0 t1) in
    t2

  let bind3 x y z t =
    let t1 = B (ident_of_binder z, bind_term z 0 t) in
    let t2 = B (ident_of_binder y, binder (bind_term y) 0 t1) in
    let t3 = B (ident_of_binder x, binder (binder (bind_term x)) 0 t2) in
    t3

  module Close (Ctxt : EXTENDABLE_CONTEXT) = struct
    let close ty (B (nm, tm)) ctxt =
      let nm, ctxt = Ctxt.extend nm ty ctxt in
      Ctxt.mk_free nm ty, close_term nm 0 tm, ctxt

    let close2 ty1 ty2 (B (nm1, B (nm2, t))) ctxt =
      let nm1, ctxt = Ctxt.extend nm1 ty1 ctxt in
      let x1 = Ctxt.mk_free nm1 ty1 in
      let ty2 = ty2 x1 in
      let nm2, ctxt = Ctxt.extend nm2 ty2 ctxt in
      let x2 = Ctxt.mk_free nm2 ty2 in
      x1, x2, (close_term nm2 0 (close_term nm1 1 t)), ctxt

    let close3 ty1 ty2 ty3 (B (nm1, B (nm2, B (nm3, t)))) ctxt =
      let nm1, ctxt = Ctxt.extend nm1 ty1 ctxt in
      let x1 = Ctxt.mk_free nm1 ty1 in
      let ty2 = ty2 x1 in
      let nm2, ctxt = Ctxt.extend nm2 ty2 ctxt in
      let x2 = Ctxt.mk_free nm2 ty2 in
      let ty3 = ty3 x1 x2 in
      let nm3, ctxt = Ctxt.extend nm3 ty3 ctxt in
      let x3 = Ctxt.mk_free nm3 ty3 in
      x1, x2, x3, close_term nm3 0 (close_term nm2 1 (close_term nm1 2 t)), ctxt
  end

end

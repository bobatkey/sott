open Syntax

module NameContext : sig
  include Syntax.EXTENDABLE_CONTEXT with type ty = unit and type tm = string

  val empty : t
end = struct
  module NameSet = Set.Make (String)

  type t = NameSet.t

  type ty = unit

  type tm = string

  let empty = NameSet.empty

  let extend nm _ t =
    let nm = Name_supply.freshen_for (fun nm -> NameSet.mem nm t) nm in
    nm, NameSet.add nm t

  let mk_free nm _ = nm
end

module Scope = struct
  include Scoping.Close (NameContext)
  let close = close ()
  let close2 = close2 () (fun _ -> ())
  let close3 = close3 () (fun _ -> ()) (fun _ _ -> ())
end

let pp_iter iter ~sep pp fmt container =
  let first = ref true in
  container |> iter begin fun a ->
    if not !first then Format.fprintf fmt sep;
    first := false;
    pp fmt a
  end

let pp_bindings iter ~sep pp fmt container =
  let first = ref true in
  container |> iter begin fun a b ->
    if not !first then Format.fprintf fmt sep;
    first := false;
    pp fmt (a,b)
  end

let pp_tag fmt =
  Format.fprintf fmt "`%s"

let rec pp_term ctxt fmt tm =
  match tm.term_data with
    | Lam term ->
       let nm, tm, ctxt = Scope.close term ctxt in
       Format.fprintf fmt
         "@[<hov>\\%s %a"
         nm
         (pp_lambdas ctxt) tm

    | Pi (s, t) ->
       let nm, t, t_ctxt = Scope.close t ctxt in
       Format.fprintf fmt
         "@[<hv>@[<hv>(%s : %a)%a"
         nm
         (pp_term ctxt) s
         (pp_pis t_ctxt) t

    | _ ->
       pp_sigma_term ctxt fmt tm

and pp_lambdas ctxt fmt tm =
  match tm.term_data with
    | Lam term ->
       let nm, tm, ctxt = Scope.close term ctxt in
       Format.fprintf fmt
         "%s %a"
         nm
         (pp_lambdas ctxt) tm
    | _ ->
       Format.fprintf fmt
         "->@ %a@]"
         (pp_term ctxt) tm

and pp_pis ctxt fmt tm =
  match tm.term_data with
    | Pi (s, t) ->
       let nm, t, t_ctxt = Scope.close t ctxt in
       Format.fprintf fmt
         "@,(%s : %a)%a"
         nm
         (pp_term ctxt) s
         (pp_pis t_ctxt) t
    | _ ->
       Format.fprintf fmt
         " ->@]@ %a@]"
         (pp_term ctxt) tm

and pp_sigma_term ctxt fmt tm =
  match tm.term_data with
    | Sigma (s, t) ->
       let nm, t, t_ctxt = Scope.close t ctxt in
       Format.fprintf fmt
         "(%s : %a) * %a"
         nm
         (pp_term ctxt) s
         (pp_term t_ctxt) t

    | _ ->
       pp_quottype_term ctxt fmt tm

and pp_quottype_term ctxt fmt tm =
  match tm.term_data with
    | QuotType (ty, r) ->
       Format.fprintf fmt
         "%a / %a"
         (pp_quottype_term ctxt) ty
         (pp_app_term ctxt)      r

    | _ ->
       pp_app_term ctxt fmt tm

and pp_app_term ctxt fmt tm =
  match tm.term_data with
    | Succ tm ->
       let rec count_succs n tm =
         match tm.term_data with
           | Zero    -> Some n
           | Succ tm -> count_succs (n+1) tm
           | _       -> None
       in
       (match count_succs 1 tm with
         | Some n ->
            Format.fprintf fmt "%d" n
         | None ->
            Format.fprintf fmt
              "Succ %a"
              (pp_base_term ctxt) tm)

    | Neutral (h, elims, _) when elims.elims_data <> Nil ->
       Format.fprintf fmt
         "@[<v>%a@]"
         (pp_elims ctxt) (h, elims)

    | _ ->
       pp_base_term ctxt fmt tm

and pp_base_term ctxt fmt tm =
  match tm.term_data with
    | Set ->
       Format.fprintf fmt "Set"
    | Bool ->
       Format.fprintf fmt "Bool"
    | True ->
       Format.fprintf fmt "True"
    | False ->
       Format.fprintf fmt "False"
    | Nat ->
       Format.fprintf fmt "Nat"
    | Zero ->
       Format.fprintf fmt "0"
    | Empty ->
       Format.fprintf fmt "Empty"
    | TyEq (t1, t2) ->
       Format.fprintf fmt
         "@[[%a@ = %a]@]"
         (pp_term ctxt) t1
         (pp_term ctxt) t2
    | TmEq { tm1; ty1; tm2; ty2 } when alpha_eq ty1 ty2 ->
       Format.fprintf fmt
         "[@[%a@ = %a@ : %a]@]"
         (pp_term ctxt) tm1
         (pp_term ctxt) tm2
         (pp_term ctxt) ty2
    | TmEq { tm1; ty1; tm2; ty2 } ->
       Format.fprintf fmt
         "[@[@[%a : %a@]@ = @[%a : %a@]]@]"
         (pp_term ctxt) tm1
         (pp_term ctxt) ty1
         (pp_term ctxt) tm2
         (pp_term ctxt) ty2
    | QuotIntro tm ->
       Format.fprintf fmt
         "[%a]"
         (pp_term ctxt) tm
    | TagType tags ->
       Format.fprintf fmt
         "{|@[%a@]|}"
         (pp_iter TagSet.iter ~sep:",@ " pp_tag) tags
    | Tag tag ->
       pp_tag fmt tag
    | Neutral (h, {elims_data=Nil}, _) ->
       pp_head ctxt fmt h

    | Pair (t1, t2) ->
       let rec pp fmt tm =
         match tm.term_data with
           | Pair (t1, t2) ->
              Format.fprintf fmt
                "%a, %a"
                (pp_term ctxt) t1
                pp             t2
           | _ ->
              Format.fprintf fmt
                "%a)"
                (pp_term ctxt) tm
       in
       Format.fprintf fmt
         "(%a, %a"
         (pp_term ctxt) t1
         pp             t2

    | Subst { ty_s; ty_t; tm_x; tm_y; tm_e } ->
       let nm, ty_t, ty_ctxt = Scope.close ty_t ctxt in
       Format.fprintf fmt
         "subst(@[<hov>@[%a,@,%s.%a,@]@,@[%a,@,%a,@,%a@]@])"
         (pp_term ctxt)    ty_s
         nm
         (pp_term ty_ctxt) ty_t
         (pp_term ctxt)    tm_x
         (pp_term ctxt)    tm_y
         (pp_term ctxt)    tm_e
    | Refl ->
       Format.fprintf fmt "refl"
    | Coh prf ->
       Format.fprintf fmt "@[<2>coherence@,(%a)@]"
         (pp_term ctxt) prf
    | Funext prf ->
       let x1, x2, xe, prf, ctxt = Scope.close3 prf ctxt in
       Format.fprintf fmt
         "@[<hov 2>funext@,(@[<v>%s %s %s.@ %a@])@]"
         x1 x2 xe
         (pp_term ctxt) prf
    | SameClass prf ->
       Format.fprintf fmt "@[<2>same-class@,(%a)@]"
         (pp_term ctxt) prf
    | Irrel ->
       Format.pp_print_string fmt "<irrel>"
    | _ ->
       Format.fprintf fmt
         "@[(%a)@]"
         (pp_term ctxt) tm

and pp_head ctxt fmt head =
  match head.head_data with
    | Bound _ ->
       failwith "internal error: bound variable got free"
    | Free_local nm | Free_global nm ->
       Format.pp_print_string fmt nm
    | Coerce { coercee; src_type; tgt_type; eq_proof } ->
       Format.fprintf fmt
         "@[<2>coerce@,(@[%a,@ %a,@ %a,@ %a@])@]"
         (pp_term ctxt) coercee
         (pp_term ctxt) src_type
         (pp_term ctxt) tgt_type
         (pp_term ctxt) eq_proof

and pp_elims ctxt fmt (head, elims) =
  match elims.elims_data with
    | Nil ->
       pp_head ctxt fmt head
    | App (elims, tm) ->
       Format.fprintf fmt
         "@[<hv2>%a@ %a@]"
         (pp_elims ctxt)     (head, elims)
         (pp_base_term ctxt) tm
    | ElimBool (elims, ty, tm_t, tm_f) ->
       let nm, ty, ty_ctxt = Scope.close ty ctxt in
       Format.fprintf fmt
         "@[<v 2>%a for %s.@[%a@] {@,@[<v 3>True ->@ %a;@]@,@[<v 3>False ->@ %a;@]@]@,}"
         (pp_elims ctxt)     (head, elims)
         nm
         (pp_term ty_ctxt)   ty
         (pp_term ctxt)      tm_t
         (pp_term ctxt)      tm_f
    | Project (elims, `fst) ->
       Format.fprintf fmt
         "%a #fst"
         (pp_elims ctxt) (head, elims)
    | Project (elims, `snd) ->
       Format.fprintf fmt
         "%a #snd"
         (pp_elims ctxt) (head, elims)
    | ElimNat (elims, ty, tm_z, tm_s) ->
       let ty_nm, ty, ty_ctxt = Scope.close ty ctxt in
       let s_nm1, s_nm2, tm_s, s_ctxt = Scope.close2 tm_s ctxt in
       Format.fprintf fmt
         "@[<v 2>%a for %s.@[%a@] {@,@[<v 3>Zero ->@ %a;@]@,@[<v 3>Succ %s %s ->@ %a;@]@]@,}"
         (pp_elims ctxt)    (head, elims)
         ty_nm
         (pp_term ty_ctxt)  ty
         (pp_term ctxt)     tm_z
         s_nm1 s_nm2
         (pp_term s_ctxt)   tm_s
    | ElimQ (elims, ty, tm, eq) ->
       let ty_nm, ty, ty_ctxt = Scope.close ty ctxt in
       let tm_nm, tm, tm_ctxt = Scope.close tm ctxt in
       let eq_nm1, eq_nm2, eq_nm3, eq, eq_ctxt = Scope.close3 eq ctxt in
       Format.fprintf fmt
         "@[<v 2>%a for %s. %a {@,@[<v 3>[%s] ->@ %a;@]@,@[<v 3>%s %s %s ->@ %a;@]@]@,}"
         (pp_elims ctxt)    (head, elims)
         ty_nm
         (pp_term ty_ctxt)  ty
         tm_nm
         (pp_term tm_ctxt)  tm
         eq_nm1 eq_nm2 eq_nm3
         (pp_term eq_ctxt)  eq
    | ElimEmp (elims, ty) ->
       Format.fprintf fmt
         "@[<v 2>%a for %a. { }@]"
         (pp_elims ctxt) (head, elims)
         (pp_term ctxt)  ty
    | ElimTag (elims, ty, clauses) ->
       let ty_nm, ty, ty_ctxt = Scope.close ty ctxt in
       Format.fprintf fmt
         "@[<v 2>%a for %s. %a {@,%a@]@,}"
         (pp_elims ctxt) (head, elims)
         ty_nm (pp_term ty_ctxt) ty
         (pp_bindings TagMap.iter ~sep:"@," (pp_clause ctxt)) clauses

and pp_clause ctxt fmt (tag, term) =
  Format.fprintf fmt
    "@[<v 3>`%s ->@ %a;@]"
    tag
    (pp_term ctxt) term
    

let pp_term fmt tm =
  (* FIXME: this ought to only work in a context, so we know what
     names are available. *)
  pp_term NameContext.empty fmt tm

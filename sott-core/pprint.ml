open Syntax

module NameContext = struct
  module NameSet = Set.Make (String)
  type t = NameSet.t
  type value = unit
  let empty = NameSet.empty
  let extend nm () t =
    let nm = Name_supply.freshen_for (fun nm -> NameSet.mem nm t) nm in
    nm, NameSet.add nm t
end

module Scope = struct
  include Scoping.Close (NameContext)
  let close = close ()
  let close2 = close2 () (fun _ -> ())
  let close3 = close3 () (fun _ -> ()) (fun _ _ -> ())
end

let rec pp_term ctxt fmt tm =
  match tm.term_data with
    | Lam term ->
       let nm, tm, ctxt = Scope.close term ctxt in
       Format.fprintf fmt
         "@[<hv>\\%s ->@ %a@]"
         nm
         (pp_term ctxt) tm

    | Pi (s, t) ->
       let nm, t, t_ctxt = Scope.close t ctxt in
       Format.fprintf fmt
         "@[<hv>(%s : %a) ->@ %a@]"
         nm
         (pp_term ctxt) s
         (pp_term t_ctxt) t

    | _ ->
       pp_sigma_term ctxt fmt tm

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
       Format.fprintf fmt
         "Succ %a"
         (pp_base_term ctxt) tm

    | Neutral (h, elims) when elims.elims_data <> Nil ->
       Format.fprintf fmt
         "@[<hov 2>%a@]"
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
       Format.fprintf fmt "Zero"
    | TyEq (t1, t2) ->
       Format.fprintf fmt
         "[%a = %a]"
         (pp_term ctxt) t1
         (pp_term ctxt) t2
    | TmEq { tm1; ty1; tm2; ty2 } ->
       Format.fprintf fmt
         "[@[@[%a :@ %a@] =@ @[%a :@ %a@]]@]"
         (pp_term ctxt) tm1
         (pp_term ctxt) ty1
         (pp_term ctxt) tm2
         (pp_term ctxt) ty2
    | QuotIntro tm ->
       Format.fprintf fmt
         "[%a]"
         (pp_term ctxt) tm
    | Neutral (h, {elims_data=Nil}) ->
       pp_head ctxt fmt h
         
    | Pair (t1, t2) ->
       Format.fprintf fmt
         "(%a, %a)"
         (pp_term ctxt) t1
         (pp_term ctxt) t2

    | Subst { ty_s; ty_t; tm_x; tm_y; tm_e } ->
       let nm, ty_t, ty_ctxt = Scope.close ty_t ctxt in
       Format.fprintf fmt
         "subst(@[%a,@,%s. %a,@,%a,@,%a,@,%a@])"
         (pp_term ctxt) ty_s
         nm
         (pp_term ty_ctxt) ty_t
         (pp_term ctxt)    tm_x
         (pp_term ctxt)    tm_y
         (pp_term ctxt)    tm_e
    | Refl ->
       Format.fprintf fmt "refl"
    | Coh prf ->
       Format.fprintf fmt "coherence(%a)"
         (pp_term ctxt) prf
    | Funext prf ->
       let x1, x2, xe, prf, ctxt = Scope.close3 prf ctxt in
       Format.fprintf fmt "funext(%s %s %s. %a)" x1 x2 xe (pp_term ctxt) prf
    | SameClass prf ->
       Format.fprintf fmt "same-class(%a)"
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
         "coerce(@[%a,@ %a,@ %a,@ %a@])"
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
         "%a %a"
         (pp_elims ctxt)     (head, elims)
         (pp_base_term ctxt) tm
    | If (elims, ty, tm_t, tm_f) ->
       let nm, ty, ty_ctxt = Scope.close ty ctxt in
       Format.fprintf fmt
         "%a@ @[<hv>@[<hv 2>by_cases@ for %s. %a@]@,{ True -> %a@,; False -> %a }@]"
         (pp_elims ctxt)     (head, elims)
         nm
         (pp_term ty_ctxt)   ty
         (pp_term ctxt)      tm_t
         (pp_term ctxt)      tm_f
    | Project (elims, `fst) ->
       Format.fprintf fmt
         "%a@ #fst"
         (pp_elims ctxt) (head, elims)
    | Project (elims, `snd) ->
       Format.fprintf fmt
         "%a@ #snd"
         (pp_elims ctxt) (head, elims)
    | ElimNat (elims, ty, tm_z, tm_s) ->
       let ty_nm, ty, ty_ctxt = Scope.close ty ctxt in
       let s_nm1, s_nm2, tm_s, s_ctxt = Scope.close2 tm_s ctxt in
       Format.fprintf fmt
         "%a@ @[<hv>@[<hv 2>#recursion@ for %s. %a@]@,{ Zero -> %a@,; Succ %s %s -> %a }@]"
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
         "%a@ @[<hv>#elimq for %s. %a@,{ [%s] -> %a@,; %s %s %s -> %a }@]"
         (pp_elims ctxt)    (head, elims)
         ty_nm
         (pp_term ty_ctxt)  ty
         tm_nm
         (pp_term tm_ctxt)  tm
         eq_nm1 eq_nm2 eq_nm3
         (pp_term eq_ctxt)  eq

let pp_term fmt tm =
  pp_term NameContext.empty fmt tm

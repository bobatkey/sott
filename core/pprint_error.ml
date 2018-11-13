let pp fmt = function
  | Checker.Type_mismatch {loc; ctxt = _; computed_ty; expected_ty} ->
     Format.fprintf fmt
       "type mismatch at %a: expected type @ @[<v 2>@,%a@,@]@ is not equal to computed type@ @[<v 2>@,%a@,@]"
       Location.pp_without_filename loc
       (* FIXME: these are meaningless without the context in which they occur *)
       Pprint.pp_term  expected_ty
       Pprint.pp_term  computed_ty

  | Checker.Types_not_equal {loc; ctxt = _; ty1; ty2} ->
     Format.fprintf fmt
       "types not equal at %a:@ @[<v 2>@,%a@,@]@ is not equal to@ @[<v 2>@,%a@,@]"
       Location.pp_without_filename loc
       (* FIXME: these are meaningless without the context in which they occur *)
       Pprint.pp_term  ty1
       Pprint.pp_term  ty2

  | Checker.Terms_not_equal {loc; ctxt = _; tm1; tm2; ty} ->
     Format.fprintf fmt
       "terms not equal at %a:@ @[<v 2>@,%a@,@]@ is not equal to@ @[<v 2>@,%a@,@]@ at type@ @[<v 2>@,%a@,@]"
       Location.pp_without_filename loc
       (* FIXME: these are meaningless without the context in which they occur *)
       Pprint.pp_term  tm1
       Pprint.pp_term  tm2
       Pprint.pp_term  ty

  | Checker.Term_is_not_a_type loc ->
     Format.fprintf fmt
       "expecting a type at %a"
       Location.pp_without_filename loc

  | Checker.Term_is_not_a_small_type loc ->
     Format.fprintf fmt
       "expecting a small type at %a"
       Location.pp_without_filename loc

  | Checker.Term_is_not_a_function {loc; _} ->
     Format.fprintf fmt
       "expecting a function at %a"
       Location.pp_without_filename loc

  | Checker.Term_is_not_a_pair {loc; _} ->
     Format.fprintf fmt
       "expecting a pair at %a"
       Location.pp_without_filename loc

  | Checker.Term_is_not_a_natural loc ->
     Format.fprintf fmt
       "expecting a natural number at %a"
       Location.pp_without_filename loc

  | Checker.Term_is_not_an_equiv_class loc ->
     Format.fprintf fmt
       "expecting an equivalence class at %a"
       Location.pp_without_filename loc

  | Checker.Term_is_not_a_valid_tag (loc, tags) ->
     Format.fprintf fmt
       "expecting a tag from the set {|@[%a@]|} at %a"
       (Pprint.pp_iter Syntax.TagSet.iter ~sep:",@ " Pprint.pp_tag) tags
       Location.pp_without_filename loc

  | Checker.Term_is_not_a_type_equality loc ->
     Format.fprintf fmt
       "expecting a type equality proof constructor at %a"
       Location.pp_without_filename loc

  | Checker.Term_is_not_a_term_equality loc ->
     Format.fprintf fmt
       "expecting a term equality proof constructor at %a"
       Location.pp_without_filename loc

  | Checker.BadSubst { loc; ctxt = _; desired_eq; proved_eq } ->
     Format.fprintf fmt
       "at %a: use of 'subst' proves the equation@ @[<v 2>@,%a@,@]@ but the equation@ @[<v 2>@,%a@,@]@ was expected."
       Location.pp_without_filename loc
       Pprint.pp_eqn                proved_eq
       Pprint.pp_eqn                desired_eq

  | Checker.BadFunext { loc; ctxt = _; ty } ->
     Format.fprintf fmt
       "at %a: attempt to use 'funext' to prove the equation@ @[<v 2>@,%a@,@]@ which is not an equation between values of function type."
       Location.pp_without_filename loc
       Pprint.pp_term               ty

  | Checker.BadCoherence { loc; ctxt = _; ty } ->
     Format.fprintf fmt
       "at %a: attempt to use 'coherence' to prove the equation@ @[<v 2>@,%a@,@]@ which is not of the right shape."
       Location.pp_without_filename loc
       Pprint.pp_term               ty

  | Checker.BadSameClass { loc; ctxt = _; ty } ->
     Format.fprintf fmt
       "at %a: attempt to use 'same-class' to prove the equation@ @[<v 2>@,%a@,@]@ which is not of the right shape."
       Location.pp_without_filename loc
       Pprint.pp_term               ty

  | Checker.BadApplication { loc; arg_loc = _; ctxt = _; ty } ->
     Format.fprintf fmt
       "Application of a non function at %a: term has type@ @[<v 2>@,%a@,@]"
       Location.pp_without_filename loc
       Pprint.pp_term               ty

  | Checker.BadProject { loc; hd_loc = _; ctxt = _; ty } ->
     Format.fprintf fmt
       "bad projection at %a: term has type@ @[<v 2>@,%a@,@]@ which does not support projection."
       Location.pp_without_filename loc
       Pprint.pp_term               ty

  | Checker.BadNatElim { loc; hd_loc = _; ctxt = _; ty } ->
     Format.fprintf fmt
       "at %a: natural number elimination applied to expression of type @[<v 2>@,%a@,@]@ which is not Nat."
       Location.pp_without_filename loc
       Pprint.pp_term               ty

  | Checker.BadQuotElim { loc; hd_loc = _; ctxt = _; ty } ->
     Format.fprintf fmt
       "at %a: quotient elimination applied to expression of type @[<v 2>@,%a@,@]@ which is not a quotient type."
       Location.pp_without_filename loc
       Pprint.pp_term               ty

  | Checker.BadTagElim { loc; hd_loc = _; ctxt = _; ty } ->
     Format.fprintf fmt
       "bad tag elimination at %a: term has type@ @[<v 2>@,%a@,@]@ which is not a tag type."
       Location.pp_without_filename loc
       Pprint.pp_term               ty

  | Checker.IncorrectTags { loc; hd_loc = _; unmatched = _; unmatchable = _ } ->
     Format.fprintf fmt
       "bad tag elimination at %a: the tags being matched do not match the possible tags of the scruntinee (FIXME)."
       Location.pp_without_filename loc

  | Checker.VarNotFound { loc; varnm }  ->
     Format.fprintf fmt
       "Variable '%s' not in scope at %a"
       varnm
       Location.pp_without_filename loc

(** Freshening of names *)

(** [freshen_for taken base_ident] returns a string [ident] such that
   [not (taken ident)] is true, and [ident] is visually related to
   [base_ident] in some way. In the current implementation, "related"
   means that [ident] will differ from [base_ident] in either the
   addition or incrementing of a numerical suffix.

    To guarantee that this function terminations no matter what
   strategy is chosen to freshen names, there must be only a finite
   number of identifiers [ident] such that [taken ident] is [true]. *)
val freshen_for : (string -> bool) -> string -> string

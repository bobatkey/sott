let get_number_suffix str =
  let rec find_split i =
    if i = 0 then 0
    else match str.[i-1] with
      | '0' .. '9' -> find_split (i-1)
      | _          -> i
  in
  let l = String.length str in
  let i = find_split l in
  if i = l then
    (str, None)
  else
    (String.sub str 0 i,
     Some (int_of_string (String.sub str i (l - i))))

let create_candidate base = function
  | None   -> base, Some 1
  | Some i -> base ^ string_of_int i, Some (i+1)

let freshen_for taken x =
  if not (taken x) then x
  else
    let rec find base suffix =
      let candidate, new_suffix = create_candidate base suffix in
      if taken candidate then find base new_suffix
      else candidate
    in
    let base, suffix = get_number_suffix x in
    find base suffix

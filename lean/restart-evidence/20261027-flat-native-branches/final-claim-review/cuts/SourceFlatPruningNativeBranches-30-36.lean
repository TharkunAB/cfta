def advance : Receipt width → Option (Caller width × Queries)
  | .complete _ caller queries _ => some (caller, queries)
  | .rejected caller queries _ => some (caller, queries)
  | .stopped _ (.ok (some []), caller, queries, _outer, _waiting) (some _) => some (caller, queries)
  | _ => none

universe u v

inductive Reaches (forest : Forest) : Nat → Nat → Nat → Prop where
  | root (lookup : read forest uv = .root size) : Reaches forest uv uv size
  | parent (lookup : read forest uv = .parent next)
      (tail : Reaches forest next representative size) : Reaches forest uv representative size

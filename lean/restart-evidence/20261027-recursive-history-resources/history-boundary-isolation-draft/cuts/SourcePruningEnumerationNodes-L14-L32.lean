
/-- Encode empty or a stored node identity. Free references have no handle. -/
def encodeNode (value : Value Symbol Guard) : Option Nat :=
  match value with
  | .empty => some 0
  | .reference _ => none
  | .node entry _ _ _ | .union entry _ _ _ | .mu entry _ _ _ => some (entry.identity + 1)

/-- Read the complete payload only for the requested canonical winner. -/
def lookupNode (heap : State Symbol Guard) (node : Nat) : Option (Value Symbol Guard) :=
  match node with
  | 0 => some .empty
  | identity + 1 =>
      match heap.nodes.issued identity with
      | none => none
      | some key =>
          match heap.nodes.table key with
          | none => none
          | some entry => if entry.identity = identity then heap.nodeRecords key else none

def decision (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (before : EnumerationExpandableIndex.Cached Symbol Constraint) : Option Next :=
  match stop with
  | none => some (EnumerationPureSelection.next (order metadata) before)
  | some rule =>
      let remaining := EnumerationIndexSelection.candidates before
      if !remaining.isEmpty && remaining.all (rule metadata) then none
      else some (EnumerationPureSelection.next (order metadata) before)

/-- Reject blocked work and otherwise retain the exact metadata and enumeration state. -/
def run (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (before : EnumerationExpandableIndex.Cached Symbol Constraint) :
    EnumerateM Symbol Constraint (Metadata Typing × Option Next) :=
  let next := decision stop order metadata before

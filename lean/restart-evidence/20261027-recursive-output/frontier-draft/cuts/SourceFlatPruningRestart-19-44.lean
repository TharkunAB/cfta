def candidates (before : Cached Symbol Constraint) : List Nat :=
  (List.range before.core.counter).filter before.expandable

/-- Keep source preference and its candidate-minus-waiting selection. -/
def next (preference : List Nat → Option Nat) (before : Cached Symbol Constraint) : Next :=
  let remaining := candidates before
  pickNext preference (if remaining.isEmpty then none
    else some (remaining.filter fun uv => (before.waiting uv).isNone))

/-- Test the stop rule on all candidates before selecting unblocked work. -/
def decision (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (before : Cached Symbol Constraint) : Option Next :=
  match stop with
  | none => some (next (order metadata) before)
  | some rule =>
      let remaining := candidates before
      if !remaining.isEmpty && remaining.all (rule metadata) then none
      else some (next (order metadata) before)

/-- Reject stuck work and otherwise retain the exact metadata and core. -/
def run (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (before : Cached Symbol Constraint) : EnumerationFlatState.Action Symbol Constraint (Metadata Typing × Option Next) :=
  let selected := decision stop order metadata before
  fun core => if selected = some .stuck then [] else [.ok ((metadata, selected), core)]

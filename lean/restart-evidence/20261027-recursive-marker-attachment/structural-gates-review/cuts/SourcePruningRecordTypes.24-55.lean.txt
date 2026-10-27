structure Metadata (Typing : Type) where
  /-- Pending template checks retain order and repeated occurrences. -/
  pending : List (Pending Symbol)
  /-- Raw type-position IDs model the source IntSet observation. -/
  types : List Nat
  /-- Raw open-program IDs use the same source set representation. -/
  openHoles : List Nat
  /-- The caller's typing state is unchanged by recording. -/
  typing : Typing

/-- The source first selects pending holes, then the first candidate outside types. -/
def typesLast (metadata : Metadata Typing) (candidates : List Nat) : Option Nat :=
  match SourcePruningTemplates.order metadata.pending candidates with
  | some uv => some uv
  | none => candidates.find? (fun uv => !metadata.types.contains uv)

/-- A type hole can stop only when no pending check contains its raw ID. -/
def atTypes (metadata : Metadata Typing) (uv : Nat) : Bool :=
  metadata.types.contains uv && metadata.pending.all (fun group => group.all (fun entry => entry.2 != uv))

/-- Classify fragment holes from the incoming raw current membership. -/
def updatedTypes (metadata : Metadata Typing) (uv : Nat) : Sum (Fragment Symbol) Nat → List Nat
  | .inl fragment => SourcePruningPositions.typePositions (metadata.types.contains uv) fragment metadata.types
  | .inr _ => metadata.types

/-- The actual callback updates only the pending checks and type-position set. -/
def recordTypes (graph : Graph Symbol Guard) (templates : List (Template.Pattern Symbol))
    (fuel : Nat) : Oracle Symbol Guard (Metadata Typing) := fun metadata uv input => do
  let types := updatedTypes metadata uv input
  let observed ← if templates.isEmpty then pure (false, metadata.pending)
    else SourcePruningOracle.oracle graph templates fuel metadata.pending uv input
  pure (observed.1, {metadata with pending := observed.2, types := types})

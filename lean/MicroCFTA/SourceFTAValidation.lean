import MicroCFTA.FTAValidation

/-!
# Current structural FTA validation

`Data.CFTA.validateFTA` checks the initial state and dangling children.
`Data.CFTA.mkFTA` first merges rows into its state map. A symbol can occur
at several arities. The optional `mixedArity` scan is a separate operation.
The older ranked-alphabet validator remains in `FTAValidation`.
-/
namespace MicroCFTA.SourceFTAValidation
open Language

variable {State Symbol : Type}

/-- Structural validation reports only a missing root or a dangling child. -/
inductive Error (State : Type) where
  | missingInitial : State → Error State
  | dangling : State → Error State

/-- Check the root first, then every child, and return the complete table. -/
def validateRows [DecidableEq State] (initial : State) (rows : FTAValidation.Rows State Symbol) :
    Except (Error State) (FTAValidation.Rows State Symbol) :=
  if initial ∈ rows.map Prod.fst then
    match FTAValidation.dangling rows with
    | some child => .error (.dangling child)
    | none => .ok rows
  else .error (.missingInitial initial)

/-- Structural validity allows a symbol at several arities. -/
def Valid (initial : State) (rows : FTAValidation.Rows State Symbol) : Prop :=
  initial ∈ rows.map Prod.fst ∧ FTAValidation.Closed rows

/-- Structural validation succeeds exactly when the root and all children exist. -/
theorem validateRows_exact [DecidableEq State] (initial : State)
    (rows : FTAValidation.Rows State Symbol) :
    validateRows initial rows = .ok rows ↔ Valid initial rows := by
  by_cases initialPresent : initial ∈ rows.map Prod.fst
  · cases missing : FTAValidation.dangling rows with
    | some child =>
        have notClosed : ¬FTAValidation.Closed rows := by
          intro closed
          have none := (FTAValidation.dangling_none rows).mpr closed
          simp [none] at missing
        simp [validateRows, initialPresent, missing, Valid, notClosed]
    | none =>
        have closed := (FTAValidation.dangling_none rows).mp missing
        simp [validateRows, initialPresent, missing, Valid, closed]
  · simp [validateRows, initialPresent, Valid]

/-- Public construction merges duplicate state rows before structural validation. -/
def mkFTA [DecidableEq State] [Ord State] (initial : State)
    (rows : FTAValidation.Rows State Symbol) : Except (Error State) (FTAValidation.Rows State Symbol) :=
  validateRows initial (FTAValidation.normalizeRows rows)

private theorem edge_owner [DecidableEq State] (rows : FTAValidation.Rows State Symbol)
    (edge : Edge State Symbol) :
    edge ∈ FTAValidation.edges rows ↔ ∃ state, edge ∈ FTAValidation.rowFor rows state := by
  constructor
  · intro present
    obtain ⟨⟨state, outgoing⟩, member, edgeMember⟩ := List.mem_flatMap.mp present
    exact ⟨state, (FTAValidation.rowFor_exact rows state edge).mpr ⟨outgoing, member, edgeMember⟩⟩
  · rintro ⟨state, present⟩
    obtain ⟨outgoing, member, edgeMember⟩ := (FTAValidation.rowFor_exact rows state edge).mp present
    exact List.mem_flatMap.mpr ⟨(state, outgoing), member, edgeMember⟩

/-- Normalization retains precisely the original edge records. -/
theorem normalized_edges [DecidableEq State] [Ord State]
    (rows : FTAValidation.Rows State Symbol) (edge : Edge State Symbol) :
    edge ∈ FTAValidation.edges (FTAValidation.normalizeRows rows) ↔
      edge ∈ FTAValidation.edges rows := by
  rw [edge_owner, edge_owner]
  constructor
  · rintro ⟨state, present⟩
    exact ⟨state, (FTAValidation.normalized_row_exact rows state edge).mp present⟩
  · rintro ⟨state, present⟩
    exact ⟨state, (FTAValidation.normalized_row_exact rows state edge).mpr present⟩

/-- Merging duplicate rows preserves structural child closure in both directions. -/
theorem normalized_closed [DecidableEq State] [Ord State]
    (rows : FTAValidation.Rows State Symbol) :
    FTAValidation.Closed (FTAValidation.normalizeRows rows) ↔ FTAValidation.Closed rows := by
  constructor
  · intro closed edge member child present
    exact (FTAValidation.normalized_keys rows child).mp
      (closed edge ((normalized_edges rows edge).mpr member) child present)
  · intro closed edge member child present
    exact (FTAValidation.normalized_keys rows child).mpr
      (closed edge ((normalized_edges rows edge).mp member) child present)

/-- Normalization preserves exactly the two structural validity conditions. -/
theorem normalized_valid [DecidableEq State] [Ord State] (initial : State)
    (rows : FTAValidation.Rows State Symbol) :
    Valid initial (FTAValidation.normalizeRows rows) ↔ Valid initial rows := by
  exact and_congr (FTAValidation.normalized_keys rows initial) (normalized_closed rows)

/-- Public construction succeeds exactly when the raw table is structurally valid. -/
theorem mkFTA_exact [DecidableEq State] [Ord State] (initial : State)
    (rows : FTAValidation.Rows State Symbol) :
    mkFTA initial rows = .ok (FTAValidation.normalizeRows rows) ↔ Valid initial rows := by
  rw [mkFTA, validateRows_exact, normalized_valid]

/-- Validation never returns a partial table. -/
theorem validateRows_returns [DecidableEq State] (initial : State)
    (rows result : FTAValidation.Rows State Symbol)
    (success : validateRows initial rows = .ok result) : result = rows := by
  unfold validateRows at success
  split at success
  · split at success
    · simp at success
    · exact (Except.ok.inj success).symm
  · simp at success

/-- Successful public construction returns the entire normalized table. -/
theorem mkFTA_returns [DecidableEq State] [Ord State] (initial : State)
    (rows result : FTAValidation.Rows State Symbol)
    (success : mkFTA initial rows = .ok result) : result = FTAValidation.normalizeRows rows :=
  validateRows_returns initial (FTAValidation.normalizeRows rows) result success

/-- Successful construction retains every finite accepted term, including cyclic rows. -/
theorem mkFTA_language [DecidableEq State] [Ord State] (initial : State)
    (rows result : FTAValidation.Rows State Symbol)
    (success : mkFTA initial rows = .ok result) (state : State) (term : Term Symbol) :
    Accepts (FTAValidation.rowFor result) state term ↔
      Accepts (FTAValidation.rowFor rows) state term := by
  rw [mkFTA_returns initial rows result success]
  exact FTAValidation.normalized_language_exact rows state term

/-- One closed state uses the same symbol as a constant and a unary constructor. -/
def mixedArityRows : FTAValidation.Rows Nat Nat :=
  [(0, [⟨7, [], fun _ => true⟩, ⟨7, [0], fun _ => true⟩])]

/-- The current structural validator accepts both arities of this symbol. -/
theorem mixed_arity_accepted : validateRows 0 mixedArityRows = .ok mixedArityRows := rfl

/-- The legacy ranked-alphabet validator rejects the same structurally valid table. -/
theorem mixed_arity_legacy_rejected :
    FTAValidation.validateRows 0 mixedArityRows = .error (.inconsistent ⟨7, 0, 1⟩) := rfl

end MicroCFTA.SourceFTAValidation

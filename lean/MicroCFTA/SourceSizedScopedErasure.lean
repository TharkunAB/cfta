import MicroCFTA.SourceSizedDeterminizationTableInput
import MicroCFTA.SourceSizedFiniteKeysTrim

/-!
# Constraint erasure after the scoped plainness check

The source checks constraints only after trimming at the query root.
Shared determinization still reads every erased original row. Agreement
on the retained rows gives the same original language at that root.

Current structural validation supplies the finite key carrier, child
closure, and root membership. No global plainness, uniform symbol arity,
or completeness of the original state type is required.
-/
namespace MicroCFTA.SourceSizedScopedErasure
open Language SourceSizedDecided SourceSizedFiniteKeys SourceDenseRows

variable {State Symbol Payload : Type} [DecidableEq State] [Ord State] [DecidableEq Payload]

/-- Scan the constraints of the structurally trimmed raw rows at the query root. -/
def plainCheck (table : SourceSizedFiniteKeys.Table State Symbol Payload)
    (root : State) (neutral : Payload) : Bool :=
  (keys table).all fun state =>
    (SourceSizedTrimGuards.trimmedRows (lookup table) (keys table) root state).all
      fun row => decide (row.constraint = neutral)

/-- Passing the actual scan proves neutrality on every retained raw row. -/
theorem checked_constraint (table : SourceSizedFiniteKeys.Table State Symbol Payload)
    (root : State) (neutral : Payload) (passed : plainCheck table root neutral = true)
    (state : State) (row : Row State Symbol Payload)
    (member : row ∈ SourceSizedTrimGuards.trimmedRows (lookup table) (keys table) root state) :
    row.constraint = neutral := by
  have stored : row ∈ lookup table state := by
    unfold SourceSizedTrimGuards.trimmedRows at member
    split at member
    · exact (List.mem_filter.mp member).1
    · simp at member
  have owner : state ∈ keys table :=
    SourceSizedDeterminizationTableInput.rows_supported table state
      (row.edge (fun _ _ => true)) (List.mem_map.mpr ⟨row, stored, rfl⟩)
  have scanned := List.all_eq_true.mp passed state owner
  exact of_decide_eq_true (List.all_eq_true.mp scanned row member)

/-- Current validation and the scoped scan justify erasure at the original query root. -/
theorem erasure_exact (table : SourceSizedFiniteKeys.Table State Symbol Payload)
    (root : State) (neutral : Payload) (holds : Payload → Term Symbol → Bool)
    (success : SourceFTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (passed : plainCheck table root neutral = true)
    (holdsNeutral : ∀ term, holds neutral term = true) (term : Term Symbol) :
    Accepts (automaton (lookup table) holds) root term ↔
      Accepts (SourceSizedDeterminizationTableInput.rows table) root term := by
  let closed := SourceSizedStructuralKeys.validated_closed table root success
  let finiteRoot : Member (keys table) :=
    ⟨root, SourceSizedStructuralKeys.validated_root table root success⟩
  have finiteExact :
      Accepts (automaton (restricted table closed) holds) finiteRoot term ↔
        Accepts (automaton (restricted table closed) (fun _ _ => true)) finiteRoot term := by
    refine SourceSizedTrimGuards.guards_exact (restricted table closed) (keys table).attach
      (member_complete (keys table)) finiteRoot holds (fun _ _ => true) ?_ term
    intro state row member candidate
    have rawMember : forget row ∈
        SourceSizedTrimGuards.trimmedRows (lookup table) (keys table) root state.val := by
      rw [← SourceSizedFiniteKeysTrim.trimmedRows_readback table closed finiteRoot state]
      exact List.mem_map.mpr ⟨row, member, rfl⟩
    have neutralRow := checked_constraint table root neutral passed state.val (forget row) rawMember
    change row.constraint = neutral at neutralRow
    change holds row.constraint candidate = true
    rw [neutralRow]
    exact holdsNeutral candidate
  exact (SourceSizedFiniteKeys.accepts_exact table closed holds finiteRoot term).symm.trans
    (finiteExact.trans
      (SourceSizedFiniteKeys.accepts_exact table closed (fun _ _ => true) finiteRoot term))

end MicroCFTA.SourceSizedScopedErasure

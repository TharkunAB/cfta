import MicroCFTA.SourceEqualityNativeDemandCellValidity

/-!
# Checked node receipts for empty and self branches

The actual source guard order selects these branches. Each body returns
without a constructor effect or recursive request. Physical source equality
derives the complete self record. Independent language gives both result
laws. Neither proof uses eager completed provenance.
-/
namespace MicroCFTA.SourceEqualityNativeDemandProvenance
open Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State

/-- A literal empty operand gives an actual checked empty-body receipt and its exact language. -/
theorem empty_body_produced [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (request : NodeRequest Symbol Guard) (state : Checked width)
    (ready : NodeReady state.native.machine request) (empty : request.left = .empty ∨ request.right = .empty) :
    NodeProduced (width := width) holds state.native.machine request .empty := by
  have guard : hasEmpty request.left request.right = true := by
    rcases empty with left | right
    · simp only [hasEmpty, left, Value.referenceOf, beq_self_eq_true, Bool.true_or]
    · simp only [hasEmpty, right, Value.referenceOf, beq_self_eq_true, Bool.or_true]
  have selected := empty_first request.domain.key request.left request.right guard
  refine ⟨state, state, 1, ready, ?_, Extension.refl _, empty_available _, Extension.refl _, ?_⟩
  · simp only [compileNode, selected, SourceEqualityNativeDemand.execute, SourceEqualityNativeDemand.step,
      SourceRecursiveIntersectionNative.step, SourceEqualityNativeDemand.lift]
  · intro _ _ _ ambient term
    rw [InternedGuardedLanguage.meaning]
    constructor
    · intro impossible; cases impossible
    · intro common
      rcases empty with left | right
      · simpa only [left, InternedGuardedLanguage.meaning] using common.1
      · simpa only [right, InternedGuardedLanguage.meaning] using common.2

/-- Physical self equality gives an actual checked body receipt for the complete original record. -/
theorem self_body_produced [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (request : NodeRequest Symbol Guard) (state : Checked width)
    (valid : SourceRecursiveIntersectionKernel.Valid state.native.machine)
    (ready : NodeReady state.native.machine request)
    (nonempty : hasEmpty request.left request.right = false)
    (noReset : reset request.domain.key request.left request.right = false)
    (same : closedSelf request.left request.right = true) :
    NodeProduced (width := width) holds state.native.machine request request.left := by
  have selected := self_first request.domain.key request.left request.right nonempty noReset same
  have records := self_record state.native.machine.heap valid.1 request.left request.right ready.2.1 ready.2.2 same
  refine ⟨state, state, 1, ready, ?_, Extension.refl _, ready.2.1, Extension.refl _, ?_⟩
  · simp only [compileNode, selected, SourceEqualityNativeDemand.execute, SourceEqualityNativeDemand.step,
      SourceRecursiveIntersectionNative.step, SourceEqualityNativeDemand.lift]
  · intro _ _ _ ambient term
    rw [records]
    exact ⟨fun accepted => ⟨accepted, accepted⟩, fun common => common.1⟩

/-- A started pure node branch completes at its captured handle without changing the physical machine. -/
theorem pure_node_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : NodeRequest Symbol Guard) (state : Checked width) (value : Value Symbol Guard)
    (pureBody : compileNode request = .pure value)
    (handle : Nat) (chosen current : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (published : lookupNode width request state.native = (.memoized handle, chosen))
    (started : demandNode handle chosen = (.evaluate request, current)) :
    SourceEqualityNativeDemand.execute 4 (.code (.node request .pure)) state =
      .done value ⟨SourceRecursiveIntersectionThunks.finishNode handle value current, state.operations⟩ := by
  simp only [SourceEqualityNativeDemand.execute, SourceEqualityNativeDemand.step,
    SourceRecursiveIntersectionNative.step, published, started, pureBody, Code.bind, SourceEqualityNativeDemand.lift]

end MicroCFTA.SourceEqualityNativeDemandProvenance

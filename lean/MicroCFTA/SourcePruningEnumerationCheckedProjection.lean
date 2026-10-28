import MicroCFTA.SourcePruningEnumerationAllocatedOriginArity
import MicroCFTA.SourcePruningEnumerationCheckedArity
import MicroCFTA.SourceEqualityAnnotationHeap

/-!
# Projection support from actual checked edge construction

The accepted constructor test supplies a noncontradictory equality accessor.
The rejected constructor returns the Top sentinel, which also projects.
Raw native readiness alone does not supply this checked-construction fact.
-/
namespace MicroCFTA.SourcePruningEnumerationCheckedProjection

/-- The actual accepted constructor check excludes a missing projection. -/
theorem accepted_projectable {Formula : Type}
    (constraint : SourceSymbolicIndex.Constraint Formula) (arity : Nat)
    (checked : SourceEqualityMkEdgeAllocation.accepted constraint arity = true) :
    SourcePruningEnumerationConstraint.project constraint ≠ none := by
  have fits : SourceEqualityMkEdgeAllocation.fits arity
      (SourceCompactGuards.sourceEqualities constraint) = true := by
    by_cases rejected : SourceEqualityMkEdgeAllocation.contradictory constraint = true
    · simp only [SourceEqualityMkEdgeAllocation.accepted, rejected, ↓reduceIte,
        Bool.false_eq_true] at checked
    · simpa only [SourceEqualityMkEdgeAllocation.accepted, rejected, Bool.false_eq_true,
        ↓reduceIte] using checked
  obtain ⟨classes, source, _bounds⟩ :=
    (SourceEqualityMkEdgeArity.fits_exact arity
      (SourceCompactGuards.sourceEqualities constraint)).mp fits
  intro missing
  simp only [SourcePruningEnumerationConstraint.project, source] at missing
  cases missing

end MicroCFTA.SourcePruningEnumerationCheckedProjection

namespace MicroCFTA.SourceCurrentAllocatedMkEdge
open InternedConstructorTemplates
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "raw" => SourceEqualityConjoinAllocation.readback
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
variable {width : Nat} [DecidableEq (EdgeKey Symbol Constraint)]

/-- Both actual checked constructor branches return a projectable edge. -/
theorem Receipt.projectable
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {symbol : Symbol} {constraint : Allocated} {children : List (Value Symbol Constraint)}
    {before after : SourceEqualityNativeDemand.State width} {result : EdgeValue Symbol Constraint}
    (receipt : Receipt formulas solver inventory symbol constraint children before result after) :
    SourcePruningEnumerationConstraint.project result.entry.key.constraint ≠ none := by
  have same := receipt.guard
  cases kept : SourceEqualityMkEdgeAllocation.accepted (raw constraint) children.length with
  | false =>
      simp only [kept, Bool.false_eq_true, ↓reduceIte] at same
      rw [same]
      change (some ([], none) : Option (List EqualityTrie.Trie × Option Constraint)) ≠ none
      intro impossible
      cases impossible
  | true =>
      simp only [kept, ↓reduceIte] at same
      rw [same]
      exact SourcePruningEnumerationCheckedProjection.accepted_projectable
        (raw constraint) children.length kept

/-- The actual raw-rejection sentinel has the empty successful projection. -/
theorem RejectReceipt.projectable
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {symbol : Symbol} {before after : SourceEqualityNativeDemand.State width}
    {result : EdgeValue Symbol Constraint}
    (receipt : RejectReceipt formulas solver inventory symbol before result after) :
    SourcePruningEnumerationConstraint.project result.entry.key.constraint ≠ none := by
  rw [receipt.guard]
  change (some ([], none) : Option (List EqualityTrie.Trie × Option Constraint)) ≠ none
  intro impossible
  cases impossible

end MicroCFTA.SourceCurrentAllocatedMkEdge

namespace MicroCFTA.SourceCurrentAllocatedParentEdge
open InternedConstructorTemplates
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable {width : Nat} [DecidableEq (EdgeKey Symbol Constraint)]

/-- The retained actual Parent construction receipt supplies projection support. -/
theorem Receipt.projectable
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {symbol : Symbol} {original : Constraint}
    {loaded : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula}
    {inherited : SourceEqualityConstraintAllocation.Value} {values : List (Value Symbol Constraint)}
    {before after : SourceEqualityNativeDemand.State width} {result : EdgeValue Symbol Constraint}
    {fourth savedFourth : SourceCurrentEmptinessMemo.Memo}
    {memo saved : SourceCurrentMemoMergeGraph.Memo Symbol Constraint} {final : EndpointMemoGateTrace.Memos}
    (receipt : Receipt formulas solver inventory symbol original loaded inherited values before result after
      fourth savedFourth memo saved final) :
    SourcePruningEnumerationConstraint.project result.entry.key.constraint ≠ none := by
  rcases receipt.construction with rejected | ⟨_children, _middle, _length, built⟩
  · exact rejected.projectable
  · exact built.projectable

end MicroCFTA.SourceCurrentAllocatedParentEdge

namespace MicroCFTA.SourcePruningEnumerationCheckedProjection
open InternedConstructorTemplates InternedProbeProvenance
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- An actual raw interner can retain a normalized but unprojectable edge.
This result concerns the raw native constructor, not the checked Haskell API. -/
theorem raw_ready_counterexample (symbol : Symbol) :
    (open scoped Classical in
    let constraint : Constraint := ⟨none, .top⟩
    let before : InternedConstructorTemplates.State Symbol Constraint := empty
    let built := run (makeEdge symbol constraint []) before
    SourceEqualityRequiredCache.Ready built.2 ∧
      SourceEqualityAnnotationHeap.Heap
        (fun guard => SourceEqualityGuardReadback.Cached guard.equalities) built.2 ∧
      InternedEdgeResidency.EdgeResident built.2 built.1 ∧
      built.1.children = [] ∧
      EnumerationState.arityAllows built.1.children.length [] = true ∧
      SourcePruningEnumerationConstraint.project built.1.entry.key.constraint = none) := by
  classical
  let constraint : Constraint := ⟨none, .top⟩
  let before : InternedConstructorTemplates.State Symbol Constraint := empty
  let built := run (makeEdge symbol constraint []) before
  have ready : SourceEqualityRequiredCache.Ready before :=
    SourceEqualityRequiredCache.constructed
      (InternedNestedConstruction.Syntax.empty : InternedNestedConstruction.Syntax Symbol Constraint)
      .empty before (by simp only [InternedFreshOrdinaryConstruction.build, before])
  have children : InternedNestedProvenance.Values before ([] : List (Value Symbol Constraint)) := by
    intro child member
    cases member
  have emitted := SourceEqualityRequiredCache.edge symbol constraint [] before ready children
  obtain ⟨_symbol, guard, exactChildren⟩ := MergedPhysicalGroupEdges.makeEdge_fields before
    ready.semantic.1.normal.facts symbol constraint [] children
  have cached : SourceEqualityGuardReadback.Cached constraint.equalities := by
    intro classes impossible
    cases impossible
  have annotations := SourceEqualityAnnotationHeap.run
    (fun guard : Constraint => SourceEqualityGuardReadback.Cached guard.equalities)
    (makeEdge symbol constraint [])
    (SourceEqualityAnnotationHeap.makeEdge _ symbol constraint [] cached)
    before (SourceEqualityAnnotationHeap.empty_heap _)
  refine ⟨emitted.1.ready, annotations, emitted.2.1, exactChildren, ?_, ?_⟩
  · rw [exactChildren]
    rfl
  · rw [guard]
    rfl

end MicroCFTA.SourcePruningEnumerationCheckedProjection

import MicroCFTA.SourcePruningOuterNarrow
import MicroCFTA.SourceCurrentAllocatedPartialInvariant
import MicroCFTA.SourceCurrentAllocatedGateFields
import MicroCFTA.SourceCurrentAllocatedProbeExposure
import MicroCFTA.SourceEqualityQueryGlobalMemos

namespace MicroCFTA.SourcePruningNativeContext
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable {Key Typing : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- A completed actual narrowing read and filtered constructor derive the full caller postcondition. -/
theorem narrowAt_post
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Caller width) (memos : Memos)
    (fits : Key → Symbol → Bool) (admits : Key → Node → Bool) (key : Key)
    (fuel : Nat) (value result : Node) (heap : State Symbol Constraint)
    (initial : Context formulas solver inventory before memos)
    (available : Available before.checked.native.machine.heap value)
    (done : SourcePruningNativeView.narrowAt fits admits fuel key value before.checked.native.machine.heap =
      .done result heap) :
    ∃ final : Memos,
      Post formulas solver inventory before
        (SourceCurrentAllocatedPartialState.advance before
          (advancePhysical before.checked ⟨heap, before.checked.operations⟩) before.fourth before.merge) final ∧
      Extends memos.unfolding final.unfolding ∧ final.query = memos.query ∧
      ∃ (rows : List (EdgeValue Symbol Constraint)) (middle : State Symbol Constraint),
        MergedFreshOrdinaryExposure.nodeEdges fuel value before.checked.native.machine.heap = .done rows middle ∧
        run (makeNode (rows.filter (SourcePruningNativeView.keeps fits admits key))) middle = (result, heap) ∧
        SourceEqualityQueryGlobalMemos.ExposureReads fuel value before.checked.native.machine.heap memos final := by
  unfold SourcePruningNativeView.narrowAt at done
  cases exposed : MergedFreshOrdinaryExposure.nodeEdges fuel value before.checked.native.machine.heap with
  | unresolved | pending | exhausted => simp only [exposed] at done; cases done
  | done rows middle =>
    have built : run (makeNode (rows.filter (SourcePruningNativeView.keeps fits admits key))) middle = (result, heap) := by
      exact Prod.ext (MergedSourceComparison.Result.done.inj (by simpa only [exposed] using done)).1
        (MergedSourceComparison.Result.done.inj (by simpa only [exposed] using done)).2
    have physicalReady := SourceCurrentAllocatedConjunctionMemo.ready before.checked initial.ready.good
      initial.ready.semantic initial.ready.costs
    have read := SourceCurrentAllocatedGateFields.read (.done fuel exposed) physicalReady available
    have selected : InternedNestedProvenance.Edges middle (rows.filter (SourcePruningNativeView.keeps fits admits key)) :=
      fun edge member => read.2 edge (List.mem_filter.mp member).1
    have constructor := SourceCurrentRequiredHeapEffects.node_constructor
      (SourceCurrentConjunctionEquality.FieldAvailable before.checked.operations)
      (rows.filter (SourcePruningNativeView.keeps fits admits key)) middle read.1.ready.semantic
      read.1.ready.costs read.1.ready.fields selected
    rw [built] at constructor
    have constructed : SourceCurrentConjunctionRowsAllocation.Effects
        ⟨middle, before.checked.operations⟩ ⟨heap, before.checked.operations⟩ :=
      ⟨constructor.1, ⟨constructor.2.1, constructor.2.2.1, physicalReady.valid, constructor.2.2.2.1⟩,
        SourceEqualityConstraintMemoAllocation.grows_refl _⟩
    have effects := read.1.trans constructed
    obtain ⟨final, calls, valid, retained⟩ := SourceEqualityQueryGlobalMemos.exposure_memos fuel value
      before.checked.native.machine.heap initial.ready.semantic initial.ready.costs available memos initial.globals
    have middleValid : EndpointMemoGateTrace.Valid middle final := by
      simpa only [exposed, MergedSourceExposure.Result.state] using valid
    have finalValid := SourceQueryUnfoldMemo.valid_grows middle heap read.1.ready.semantic constructor.1 final middleValid
    have readProbes := SourceCurrentAllocatedProbeExposure.read_heap (.done fuel exposed)
      initial.ready.semantic available initial.probes
    have finalProbes := InternedFreshOrdinaryProbeHeap.node
      (rows.filter (SourcePruningNativeView.keeps fits admits key)) middle readProbes
    rw [built] at finalProbes
    let checked := advancePhysical before.checked ⟨heap, before.checked.operations⟩
    have afterContext : Context formulas solver inventory
        (SourceCurrentAllocatedPartialState.advance before checked before.fourth before.merge) final := by
      refine ⟨SourceCurrentConjunctionClassScan.advance_ready before.checked _ initial.ready effects,
        initial.admitted.advance _ (SourceCurrentAllocatedQueryMemo.advance_extension before.checked _ effects),
        initial.sound.advance formulas solver checked before.fourth before.merge effects,
        initial.stored.grows effects.keeps, initial.covered,
        SourceCurrentEmptinessMemo.grows formulas solver effects.keeps before.fourth initial.correct,
        finalValid, finalProbes⟩
    exact ⟨final, ⟨afterContext, effects, extends_refl _, fun _ _ found => found⟩,
      retained, calls.2, rows, middle, rfl, built, calls⟩

/-- Mu and type skips or the actual filtered read derive the outer narrowing caller postcondition. -/
theorem outer_post
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Caller width) (memos : Memos)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (metadata : SourcePruningRecordTypes.Metadata Typing) (fuel uv : Nat) (value result : Node)
    (heap : State Symbol Constraint)
    (initial : Context formulas solver inventory before memos)
    (available : Available before.checked.native.machine.heap value)
    (done : SourcePruningOuterNarrow.narrow holeKey fits admits metadata fuel uv value before.checked.native.machine.heap =
      .done result heap) :
    ∃ final : Memos,
      Post formulas solver inventory before
        (SourceCurrentAllocatedPartialState.advance before
          (advancePhysical before.checked ⟨heap, before.checked.operations⟩) before.fourth before.merge) final ∧
      Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  have skipped (same : result = value ∧ heap = before.checked.native.machine.heap) :
      ∃ final : Memos,
        Post formulas solver inventory before
          (SourceCurrentAllocatedPartialState.advance before
            (advancePhysical before.checked ⟨heap, before.checked.operations⟩) before.fourth before.merge) final ∧
        Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
    rcases same with ⟨rfl, rfl⟩
    exact ⟨memos, Post.refl initial, extends_refl _, rfl⟩
  by_cases typed : uv ∈ metadata.types
  · apply skipped
    have pureDone := SourcePruningOuterNarrow.narrow_type holeKey fits admits metadata fuel uv value
      before.checked.native.machine.heap typed
    have parts := MergedSourceComparison.Result.done.inj (pureDone.symm.trans done)
    exact ⟨parts.1.symm, parts.2.symm⟩
  · cases value with
    | mu =>
        have parts := MergedSourceComparison.Result.done.inj done
        exact skipped ⟨parts.1.symm, parts.2.symm⟩
    | empty | reference | node | union =>
        have actual : SourcePruningNativeView.narrowAt fits admits fuel (holeKey metadata.typing uv) _
            before.checked.native.machine.heap = .done result heap := by
          simpa only [SourcePruningOuterNarrow.narrow, List.contains_eq_false.mpr typed, Bool.false_eq_true, ite_false] using done
        obtain ⟨final, post, retained, query, _receipt⟩ := narrowAt_post formulas solver inventory before memos
          fits admits (holeKey metadata.typing uv) fuel _ result heap initial available actual
        exact ⟨final, post, retained, query⟩

end MicroCFTA.SourcePruningNativeContext

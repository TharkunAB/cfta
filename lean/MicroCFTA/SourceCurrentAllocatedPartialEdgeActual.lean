import MicroCFTA.SourceCurrentAllocatedPartialSourceReads
import MicroCFTA.SourceCurrentAllocatedPartialEdgeCall
import MicroCFTA.SourceCurrentAllocatedProbeActual

/-!
# Actual current reduced-edge calls with source-aligned reads

The supplied parent schedule derives its own language, global validity,
and filtered probes. Actual evaluation finishes its exact running owner.
The input contains only initial invariants and reached Scan word checks.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialEdgeActual
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialMemoSound (Sound EdgeLaw)
open SourceCurrentAllocatedPartialEdgeCall (Receipt)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Edge" => EdgeValue Symbol Guard
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "GlobalsValid" => EndpointMemoGateTrace.Valid
local notation "Resident" => InternedEdgeResidency.EdgeResident
local notation "ProbeHeap" => InternedFreshOrdinaryProbeHeap.Heap
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

/-- Only a reached live field load selects its actual Scan word checks. -/
def Ranges (budget : Nat) (request : EdgeRequest) (before : Caller width) : Prop :=
  SourceEqualityMkEdgeAllocation.contradictory request.value.entry.key.constraint = false →
  ∀ loaded : Allocated,
    SourceEqualityConstraintFieldLookup.load request.value.entry.key.constraint before.checked.operations.constraints =
      .ok (some loaded) →
    SourceCurrentAllocatedLocalReductionActual.Ranges budget loaded request.inherited request.value.children
      before.checked before.fourth

/-- A result hit does not demand a parent range plan. -/
def CallRanges (budget : Nat) (request : EdgeRequest) (before : Caller width) : Prop :=
  ∀ handle original running,
    beginEdge request before = (handle, .evaluate original, running) → Ranges budget original running

/-- The supplied body derives its own result law and preserves both result tables and probes. -/
theorem edge_body (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    {budget : Nat} {request : EdgeRequest} {before after : Caller width} {result : Edge}
    {actual : EdgeBody budget request before result after} {memos final : Memos}
    (reads : SourceCurrentAllocatedPartialSourceReads.EdgeBodyReads formulas solver actual memos final)
    (ready : Ready before.checked) (admitted : At formulas solver inventory before.checked)
    (sound : Sound formulas solver before)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.checked.native.machine.heap before.fourth)
    (stored : SourceCurrentMemoMergeEffects.Stored before.checked.native.machine.heap before.merge)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient before.merge)
    (ranges : Ranges budget request before) (valid : GlobalsValid before.checked.native.machine.heap memos)
    (probes : ProbeHeap before.checked.native.machine.heap) :
    ∃ next, Receipt formulas solver next request before result after final ∧
      after.edgeResults = before.edgeResults ∧ ProbeHeap after.checked.native.machine.heap := by
  cases reads with
  | parent parentReads =>
      rename_i edge loaded originalInherited checked fourth merge field parent
      have live : SourceEqualityMkEdgeAllocation.contradictory edge.entry.key.constraint = false →
          SourceEqualityGuardReadback.Cached edge.entry.key.constraint.equalities ∧
          SourceEqualityConstraintFieldLookup.load edge.entry.key.constraint before.checked.operations.constraints = .ok (some loaded) ∧
          SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints originalInherited ∧
          InternedNestedProvenance.Values before.checked.native.machine.heap edge.children ∧
          SourceCurrentAllocatedLocalReductionActual.Ranges budget loaded originalInherited edge.children before.checked before.fourth := by
        intro test
        exact ⟨(ready.good.fields edge.entry.key edge resident).1, field test, inherited,
          ready.semantic.ready.semantic.1.normal.facts.cached.edges _ edge resident, ranges test loaded (field test)⟩
      obtain ⟨next, receipt⟩ := SourceCurrentAllocatedParentEdgeActual.verified formulas solver inventory parentReads
        ready admitted live correct stored covered valid
      have finalProbes := SourceCurrentAllocatedProbeParent.parent_heap formulas solver inventory parentReads
        ready admitted live correct stored covered valid probes
      have law : EdgeLaw formulas solver ⟨originalInherited, edge⟩ result := by
        intro ambient term
        have input := InternedGuardedLanguage.edgeMeaning_all (SourceEqualityPCSGuard.holds formulas solver) ambient edge term
        change InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient edge term ↔
          SourceCurrentAllocatedParentEdge.RawMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient
            edge.entry.key.symbol edge.entry.key.constraint edge.children term at input
        exact ⟨fun accepted => input.mpr ((receipt.language ambient term).1 accepted),
          fun satisfied => ((receipt.language ambient term).2 satisfied).trans input.symm⟩
      exact ⟨next, ⟨receipt.ready, receipt.admitted,
        sound.advance formulas solver checked fourth merge receipt.effects, receipt.effects, receipt.resident,
        receipt.stored, receipt.covered, receipt.retained, receipt.globals, receipt.correct, receipt.fourthRetained, rfl, law⟩,
        rfl, finalProbes⟩

/-- A supplied completed call finishes its own owner and derives the candidate law from its physical key. -/
theorem edge_call (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    {budget : Nat} {request : EdgeRequest} {before after : Caller width} {result : Edge}
    {actual : EdgeCall budget request before result after} {memos final : Memos}
    (reads : SourceCurrentAllocatedPartialSourceReads.EdgeCallReads formulas solver actual memos final)
    (ready : Ready before.checked) (admitted : At formulas solver inventory before.checked)
    (sound : Sound formulas solver before)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.checked.native.machine.heap before.fourth)
    (stored : SourceCurrentMemoMergeEffects.Stored before.checked.native.machine.heap before.merge)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient before.merge)
    (ranges : CallRanges budget request before) (valid : GlobalsValid before.checked.native.machine.heap memos)
    (probes : ProbeHeap before.checked.native.machine.heap) :
    ∃ next, Receipt formulas solver next request before result after final ∧ ProbeHeap after.checked.native.machine.heap := by
  cases reads with
  | hit =>
      rename_i handle started
      obtain ⟨same, available, law⟩ := SourceCurrentAllocatedPartialMemoSound.beginEdge_ready_sound formulas solver
        request before sound ready.good.operations.constraints ready.semantic.ready.semantic.1.normal.facts.coherent
        inherited resident handle result after started
      subst after
      exact ⟨inventory, ⟨ready, admitted, sound,
        SourceCurrentConjunctionRowsAllocation.Effects.refl _
          (SourceCurrentAllocatedConjunctionMemo.ready before.checked ready.good ready.semantic ready.costs),
        available, stored, covered, extends_refl _, valid, correct, (fun _ _ found => found), rfl, law⟩, probes⟩
  | evaluate bodyReads =>
      rename_i original running middle handle started body
      obtain ⟨runningSound, cell, owner, key⟩ :=
        SourceCurrentAllocatedPartialMemoSound.beginEdge_evaluate_sound formulas solver request before sound inherited resident
          handle original running started
      have components := beginEdge_components request before
      rw [started] at components
      dsimp only at components
      obtain ⟨checkedSame, mergeSame, fourthSame, nodesSame⟩ := components
      have runningReady : Ready running.checked := by simpa only [checkedSame] using ready
      obtain ⟨next, receipt, tables, finalProbes⟩ := edge_body formulas solver inventory bodyReads runningReady
        (by simpa only [checkedSame] using admitted) runningSound owner.inherited owner.input
        (by simpa only [checkedSame, fourthSame] using correct)
        (by simpa only [checkedSame, mergeSame] using stored)
        (by simpa only [checkedSame, mergeSame] using covered)
        (ranges handle original running started) (by simpa only [checkedSame] using valid)
        (by simpa only [checkedSame] using probes)
      have current : middle.edgeResults.cells handle = some ⟨original, .evaluating⟩ := by rw [tables]; exact cell
      have completed := SourceCurrentAllocatedPartialMemoSound.finishEdge_sound formulas solver handle original result middle
        receipt.sound current receipt.resident receipt.language
      have law := SourceCurrentAllocatedPartialMemoSound.EdgeLaw.of_key formulas solver
        running.checked.operations.constraints running.checked.native.machine.heap original request result
        runningReady.good.operations.constraints runningReady.semantic.ready.semantic.1.normal.facts.coherent
        owner.inherited (by simpa only [checkedSame] using inherited)
        owner.input (by simpa only [checkedSame] using resident) key receipt.language
      refine ⟨next, ⟨receipt.ready, receipt.admitted, completed, ?_, receipt.resident, receipt.stored,
        receipt.covered, ?_, receipt.globals, receipt.correct, ?_, ?_, law⟩, finalProbes⟩
      · simpa only [finishEdge, checkedSame] using receipt.effects
      · simpa only [finishEdge, mergeSame] using receipt.retained
      · simpa only [finishEdge, fourthSame] using receipt.fourthRetained
      · exact receipt.nodes.trans nodesSame

end MicroCFTA.SourceCurrentAllocatedPartialEdgeActual

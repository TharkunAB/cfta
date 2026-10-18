import MicroCFTA.SourceCurrentLowerOperationInvariants
import MicroCFTA.SourceCurrentAllocatedPartialWorker
import MicroCFTA.InternedFreshOrdinaryProbeHeap

/-!
# Complete Mu reconstruction from initial filtered probes

The physical probe invariant is an initial cache fact. Actual source
construction derives it. Residency then supplies both fixed filters.
Reconstruction returns the exact smart cleanup and leaves the heap intact.
The outer node body retains the full caller at every outer bound.
-/
namespace MicroCFTA.SourceCurrentMuReconstructionEffects
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedBinderProtocol (NodeKey)

/-- Actual closed source construction derives the physical probe invariant. -/
theorem constructed [DecidableEq (EdgeKey Symbol Guard)]
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap) :
    InternedFreshOrdinaryProbeHeap.Heap heap := by
  simpa only [built, Outcome.state] using InternedFreshOrdinaryProbeHeap.closed_heap expression

/-- An initially resident Mu completes with exact cleanup and no cache effects. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)]
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (heap : State Symbol Guard) (coherent : InternedRecordCoherence.Coherent heap)
    (probes : InternedFreshOrdinaryProbeHeap.Heap heap)
    (available : Available heap (.mu entry body depth ordinary)) :
    SourceEqualityMuReconstruction.rebuild entry body depth ordinary heap =
      .done (cleanup (.mu entry body depth ordinary)) heap ∧
      Available heap (cleanup (.mu entry body depth ordinary)) :=
  ⟨SourceEqualityMuReconstruction.completed entry body depth ordinary heap coherent available
      (InternedFreshOrdinaryProbeHeap.resident heap probes entry body depth ordinary available),
    InternedConstructionProvenance.cleanup_available _ available⟩

local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Good" => SourceCurrentNativeOperationHeap.Good
local notation "Effect" => SourceCurrentLowerOperationInvariants.Effect

/-- Completion retains the initial checked invariant and gives the exact available result. -/
theorem physical [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (before : Checked width) (good : Good before)
    (probes : InternedFreshOrdinaryProbeHeap.Heap before.native.machine.heap)
    (available : Available before.native.machine.heap (.mu entry body depth ordinary)) :
    SourceEqualityMuReconstruction.rebuild entry body depth ordinary before.native.machine.heap =
      .done (cleanup (.mu entry body depth ordinary)) before.native.machine.heap ∧
      Effect before before ∧
      Available before.native.machine.heap (cleanup (.mu entry body depth ordinary)) := by
  have called := complete entry body depth ordinary before.native.machine.heap
    good.heap.semantic.1.normal.facts.coherent probes available
  exact ⟨called.1,SourceCurrentLowerOperationInvariants.Effect.refl before good,called.2⟩

/-- The literal Mu node body completes at every bound and retains the entire caller. -/
theorem node_body [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    [DecidableEq (Value Symbol Guard)] {width : Nat}
    (fuel g s r e p h m c n budget : Nat)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (inherited : SourceEqualityConstraintAllocation.Value) (before : Caller width)
    (good : Good before.checked)
    (probes : InternedFreshOrdinaryProbeHeap.Heap before.checked.native.machine.heap)
    (available : Available before.checked.native.machine.heap (.mu entry body depth ordinary)) :
    SourceCurrentAllocatedPartialWorker.nodeBody fuel g s r e p h m c n budget
      ⟨inherited,.mu entry body depth ordinary⟩ before =
      .done (cleanup (.mu entry body depth ordinary)) before := by
  have actual := (physical entry body depth ordinary before.checked good probes available).1
  simp only [SourceCurrentAllocatedPartialWorker.nodeBody,actual]
  rfl

end MicroCFTA.SourceCurrentMuReconstructionEffects

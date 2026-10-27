import MicroCFTA.SourceCurrentAllocatedPartialStepEffects
import MicroCFTA.SourceCurrentAllocatedMuRebuild
import MicroCFTA.SourcePruningEnumerationArityOrigins

/-!
# Arity at actual recursive worker allocation steps

Inherited prefixes and indexed descent retain the literal native heap.
A resident binder rebuild returns its checked cleanup at the same heap.
Each result uses the actual returned state.
-/
namespace MicroCFTA.SourcePruningEnumerationPartialStepArity
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationArityOrigins (Heap)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
variable {width : Nat}

/-- The literal completed resident binder retains arity at its own returned heap. -/
theorem binder_heap [DecidableEq (EdgeKey Symbol Guard)]
    {entry : Cache.Interned InternedBinderProtocol.NodeKey} {body depth ordinary result : Node}
    {before : Checked width} {after : State Symbol Guard}
    (ready : SourceCurrentConjunctionClassScan.Ready before)
    (probes : InternedFreshOrdinaryProbeHeap.Heap before.native.machine.heap)
    (available : Available before.native.machine.heap (.mu entry body depth ordinary))
    (actual : SourceEqualityMuReconstruction.rebuild entry body depth ordinary before.native.machine.heap =
      .done result after)
    (heap : Heap before.native.machine.heap) : Heap after := by
  have same := (SourceCurrentAllocatedMuRebuild.actual_rebuild before ready probes entry body depth ordinary
    available result after actual).2
  rw [same]
  exact heap

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- Inherited constraint allocation retains every native edge record. -/
theorem prefix_heap (before : Caller width) (edge : Edge) (inherited : EqValue)
    (heap : Heap before.checked.native.machine.heap) :
    Heap (SourceCurrentAllocatedPartialGraph.prefixState before edge inherited).checked.native.machine.heap :=
  heap

/-- Indexed descent changes operations at the literal unchanged constructor heap. -/
theorem descent_heap (before : Caller width) (combined : EqValue) (index : Nat)
    (heap : Heap before.checked.native.machine.heap) :
    Heap (SourceCurrentAllocatedPartialGraph.descend before combined index).2.checked.native.machine.heap :=
  heap

end MicroCFTA.SourcePruningEnumerationPartialStepArity

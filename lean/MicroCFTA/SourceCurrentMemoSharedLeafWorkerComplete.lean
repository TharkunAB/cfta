import MicroCFTA.SourceCurrentMemoSharedLeafWorkerProofs

/-!
# Finite executable shared leaves from original selected path domains

Actual force and leaf range plans derive completed graphs. Those graphs
supply sufficient worker bounds for the same result and complete shared
state. Unselected ordinary siblings may remain open.
-/
namespace MicroCFTA.SourceCurrentMemoSharedLeafWorkerComplete
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityProjectionPathDomain
open SourceCurrentMemoSharedTargetState SourceCurrentMemoSharedTargetForce SourceCurrentMemoSharedTargetLeaf
open SourceCurrentMemoSharedLeafWorker SourceCurrentMemoSharedLeafWorkerProofs

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
variable (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))

/-- Original selected domains and actual force ranges derive one stable executable target force. -/
theorem force_complete (base : InternedConstructorTemplates.State Symbol Guard) (known : Values base originals)
    (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) originals)
    (path : EqualityNormalize.Path) (member : path ∈ record.paths) (before : State width Symbol Guard)
    (ready : Ready emptyGuard conjoin clear top record originals base before)
    (ranges : ForceRanges emptyGuard conjoin clear top record originals path before) :
    ∃ value after, ∃ _actual : Force emptyGuard conjoin clear top record originals path before value after,
      Ready emptyGuard conjoin clear top record originals base after ∧ Keeps before.native.machine.heap after.native.machine.heap ∧
      Available after.native.machine.heap value ∧ value.free = [] ∧ after.targets path = some value ∧ Retains before after ∧
      StableRun (fun p h w c n => force emptyGuard conjoin clear top p h w c n record originals path before) value after := by
  obtain ⟨value, after, actual, finalReady, kept, available, closed, present, retained⟩ :=
    SourceCurrentMemoSharedTargetForce.complete emptyGuard conjoin clear top record originals base known domains path member before ready ranges
  exact ⟨value, after, actual, finalReady, kept, available, closed, present, retained,
    force_stable emptyGuard conjoin clear top record originals actual⟩

/-- Original selected domains and reached native checks derive a stable executable shared leaf. -/
theorem leaf_complete (base : InternedConstructorTemplates.State Symbol Guard) (known : Values base originals)
    (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) originals)
    (path : EqualityNormalize.Path) (member : path ∈ record.paths) (input : Value Symbol Guard) (before : State width Symbol Guard)
    (ready : Ready emptyGuard conjoin clear top record originals base before)
    (ranges : LeafRanges emptyGuard conjoin clear top record originals path input before)
    (available : Available before.native.machine.heap input) (closed : input.free = []) :
    ∃ value after, ∃ _actual : Leaf emptyGuard conjoin clear top record originals path input before value after,
      Ready emptyGuard conjoin clear top record originals base after ∧ Keeps before.native.machine.heap after.native.machine.heap ∧
      Available after.native.machine.heap value ∧ value.free = [] ∧ Retains before after ∧
      StableRun (fun p h w c n => leaf emptyGuard conjoin clear top p h w c n record originals path input before) value after := by
  obtain ⟨value, after, actual, finalReady, kept, resultAvailable, resultClosed, retained⟩ :=
    SourceCurrentMemoSharedTargetLeaf.complete emptyGuard conjoin clear top record originals base known domains
      path member input before ready ranges available closed
  exact ⟨value, after, actual, finalReady, kept, resultAvailable, resultClosed, retained,
    leaf_stable emptyGuard conjoin clear top record originals actual⟩

end MicroCFTA.SourceCurrentMemoSharedLeafWorkerComplete
